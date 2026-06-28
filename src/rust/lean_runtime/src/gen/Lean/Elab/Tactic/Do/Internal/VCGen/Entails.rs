// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Entails
// Imports: Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Util Lean.Meta.Sym.Util
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
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
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_12,
    lean_apply_13, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value:
    LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value
        ) as *mut LeanObject,
        515334035361346902 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value
        ) as *mut LeanObject,
        11963640885769744415 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value
        ) as *mut LeanObject,
        5695465360175800255 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value) as *mut LeanObject,17808102113152393460 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value) as *mut LeanObject,7198879216713715016 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value) as *mut LeanObject,717208579114757920 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value
        ) as *mut LeanObject,
        16895493190937329785 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 32, 115, 116, 97, 116, 101, 32, 97, 116, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 100, 101, 115, 112, 105, 116, 101, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 115, 112, 101, 99, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value
        ) as *mut LeanObject,
        16366591063295091858 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value
        ) as *mut LeanObject,
        7100147834070349651 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value:
    LeanStringObject<18> = LeanStringObject {
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
        101, 110, 116, 97, 105, 108, 115, 95, 110, 105, 108, 95, 105, 110, 116, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value
        ) as *mut LeanObject,
        15111254451868281553 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value:
    LeanStringObject<17> = LeanStringObject {
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
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value) as *mut LeanObject,16216700489815045332 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value
) as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(
    mut v_x_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v___y_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2139_);
    lean_inc_ref(v___y_2138_);
    lean_inc(v___y_2137_);
    lean_inc_ref(v___y_2136_);
    lean_inc(v___y_2135_);
    lean_inc(v___y_2134_);
    lean_inc_ref(v___y_2133_);
    v___x_2145_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_2145_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed(
    mut v_x_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(v_x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    lean_dec(v___y_2153_);
    lean_dec_ref(v___y_2152_);
    lean_dec(v___y_2151_);
    lean_dec_ref(v___y_2150_);
    lean_dec(v___y_2149_);
    lean_dec(v___y_2148_);
    lean_dec_ref(v___y_2147_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(
    mut v_mvarId_2160_: *mut LeanObject,
    mut v_x_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2168_);
                lean_inc_ref(v___y_2167_);
                lean_inc(v___y_2166_);
                lean_inc_ref(v___y_2165_);
                lean_inc(v___y_2164_);
                lean_inc(v___y_2163_);
                lean_inc_ref(v___y_2162_);
                v___f_2174_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                lean_closure_set(v___f_2174_, 0, v_x_2161_);
                lean_closure_set(v___f_2174_, 1, v___y_2162_);
                lean_closure_set(v___f_2174_, 2, v___y_2163_);
                lean_closure_set(v___f_2174_, 3, v___y_2164_);
                lean_closure_set(v___f_2174_, 4, v___y_2165_);
                lean_closure_set(v___f_2174_, 5, v___y_2166_);
                lean_closure_set(v___f_2174_, 6, v___y_2167_);
                lean_closure_set(v___f_2174_, 7, v___y_2168_);
                v___x_2175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2160_,
                    v___f_2174_,
                    v___y_2169_,
                    v___y_2170_,
                    v___y_2171_,
                    v___y_2172_,
                );
                if lean_obj_tag(v___x_2175_) == 0 {
                    return v___x_2175_;
                } else {
                    v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
                    v_isSharedCheck_2183_ = (!lean_is_exclusive(v___x_2175_)) as u8;
                    if v_isSharedCheck_2183_ == 0 {
                        v___x_2178_ = v___x_2175_;
                        v_isShared_2179_ = v_isSharedCheck_2183_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2176_);
                        lean_dec(v___x_2175_);
                        v___x_2178_ = lean_box(0);
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
                    v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
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
    mut v_mvarId_2184_: *mut LeanObject,
    mut v_x_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v___y_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_2184_, v_x_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
    lean_dec(v___y_2196_);
    lean_dec_ref(v___y_2195_);
    lean_dec(v___y_2194_);
    lean_dec_ref(v___y_2193_);
    lean_dec(v___y_2192_);
    lean_dec_ref(v___y_2191_);
    lean_dec(v___y_2190_);
    lean_dec_ref(v___y_2189_);
    lean_dec(v___y_2188_);
    lean_dec(v___y_2187_);
    lean_dec_ref(v___y_2186_);
    return v_res_2198_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(
    mut v_00_u03b1_2199_: *mut LeanObject,
    mut v_mvarId_2200_: *mut LeanObject,
    mut v_x_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_2200_, v_x_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
    return v___x_2214_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___boxed(
    mut v_00_u03b1_2215_: *mut LeanObject,
    mut v_mvarId_2216_: *mut LeanObject,
    mut v_x_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2230_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2228_);
    lean_dec_ref(v___y_2227_);
    lean_dec(v___y_2226_);
    lean_dec_ref(v___y_2225_);
    lean_dec(v___y_2224_);
    lean_dec_ref(v___y_2223_);
    lean_dec(v___y_2222_);
    lean_dec_ref(v___y_2221_);
    lean_dec(v___y_2220_);
    lean_dec(v___y_2219_);
    lean_dec_ref(v___y_2218_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(
    mut v_msgData_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2237_ = lean_st_ref_get(v___y_2235_);
    v_env_2238_ = lean_ctor_get(v___x_2237_, 0);
    lean_inc_ref(v_env_2238_);
    lean_dec(v___x_2237_);
    v___x_2239_ = lean_st_ref_get(v___y_2233_);
    v_mctx_2240_ = lean_ctor_get(v___x_2239_, 0);
    lean_inc_ref(v_mctx_2240_);
    lean_dec(v___x_2239_);
    v_lctx_2241_ = lean_ctor_get(v___y_2232_, 2);
    v_options_2242_ = lean_ctor_get(v___y_2234_, 2);
    lean_inc_ref(v_options_2242_);
    lean_inc_ref(v_lctx_2241_);
    v___x_2243_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2243_, 0, v_env_2238_);
    lean_ctor_set(v___x_2243_, 1, v_mctx_2240_);
    lean_ctor_set(v___x_2243_, 2, v_lctx_2241_);
    lean_ctor_set(v___x_2243_, 3, v_options_2242_);
    v___x_2244_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2244_, 0, v___x_2243_);
    lean_ctor_set(v___x_2244_, 1, v_msgData_2231_);
    v___x_2245_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0___boxed(
    mut v_msgData_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msgData_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
    lean_dec(v___y_2250_);
    lean_dec_ref(v___y_2249_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(
    mut v_msg_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2259_ = lean_ctor_get(v___y_2256_, 5);
                v___x_2260_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msg_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
                v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
                v_isSharedCheck_2269_ = (!lean_is_exclusive(v___x_2260_)) as u8;
                if v_isSharedCheck_2269_ == 0 {
                    v___x_2263_ = v___x_2260_;
                    v_isShared_2264_ = v_isSharedCheck_2269_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2261_);
                    lean_dec(v___x_2260_);
                    v___x_2263_ = lean_box(0);
                    v_isShared_2264_ = v_isSharedCheck_2269_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2259_);
                v___x_2265_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2265_, 0, v_ref_2259_);
                lean_ctor_set(v___x_2265_, 1, v_a_2261_);
                if v_isShared_2264_ == 0 {
                    lean_ctor_set_tag(v___x_2263_, 1);
                    lean_ctor_set(v___x_2263_, 0, v___x_2265_);
                    v___x_2267_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
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
    mut v_msg_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
    v_res_2276_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(
            v_msg_2270_,
            v___y_2271_,
            v___y_2272_,
            v___y_2273_,
            v___y_2274_,
        );
    lean_dec(v___y_2274_);
    lean_dec_ref(v___y_2273_);
    lean_dec(v___y_2272_);
    lean_dec_ref(v___y_2271_);
    return v_res_2276_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(
    mut v_f_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2291_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut v_a_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2290_ = lean_st_ref_get(v___y_2280_);
                v_debug_2291_ = lean_ctor_get_uint8(
                    v___x_2290_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2290_);
                if v_debug_2291_ == 0 {
                    v___y_2287_ = v___y_2280_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_f_2277_);
                    v___x_2292_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_2277_,
                        v___y_2279_,
                        v___y_2280_,
                        v___y_2281_,
                        v___y_2282_,
                        v___y_2283_,
                        v___y_2284_,
                    );
                    if lean_obj_tag(v___x_2292_) == 0 {
                        lean_dec_ref_known(v___x_2292_, 1);
                        lean_inc_ref(v_a_2278_);
                        v___x_2293_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_2278_,
                            v___y_2279_,
                            v___y_2280_,
                            v___y_2281_,
                            v___y_2282_,
                            v___y_2283_,
                            v___y_2284_,
                        );
                        if lean_obj_tag(v___x_2293_) == 0 {
                            lean_dec_ref_known(v___x_2293_, 1);
                            v___y_2287_ = v___y_2280_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_a_2278_);
                            lean_dec_ref(v_f_2277_);
                            v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
                            v_isSharedCheck_2301_ = (!lean_is_exclusive(v___x_2293_)) as u8;
                            if v_isSharedCheck_2301_ == 0 {
                                v___x_2296_ = v___x_2293_;
                                v_isShared_2297_ = v_isSharedCheck_2301_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2294_);
                                lean_dec(v___x_2293_);
                                v___x_2296_ = lean_box(0);
                                v_isShared_2297_ = v_isSharedCheck_2301_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_a_2278_);
                        lean_dec_ref(v_f_2277_);
                        v_a_2302_ = lean_ctor_get(v___x_2292_, 0);
                        v_isSharedCheck_2309_ = (!lean_is_exclusive(v___x_2292_)) as u8;
                        if v_isSharedCheck_2309_ == 0 {
                            v___x_2304_ = v___x_2292_;
                            v_isShared_2305_ = v_isSharedCheck_2309_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2302_);
                            lean_dec(v___x_2292_);
                            v___x_2304_ = lean_box(0);
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
                    v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
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
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
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
    mut v_f_2310_: *mut LeanObject,
    mut v_a_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2319_: *mut LeanObject = core::ptr::null_mut();
    v_res_2319_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2310_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    lean_dec(v___y_2317_);
    lean_dec_ref(v___y_2316_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    lean_dec(v___y_2313_);
    lean_dec_ref(v___y_2312_);
    return v_res_2319_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(
    mut v_f_2320_: *mut LeanObject,
    mut v_a_u2081_2321_: *mut LeanObject,
    mut v_a_u2082_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2320_, v_a_u2081_2321_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
    if lean_obj_tag(v___x_2335_) == 0 {
        let mut v_a_2336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
        v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
        lean_inc(v_a_2336_);
        lean_dec_ref_known(v___x_2335_, 1);
        v___x_2337_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_2336_, v_a_u2082_2322_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
        return v___x_2337_;
    } else {
        lean_dec_ref(v_a_u2082_2322_);
        return v___x_2335_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2___boxed(
    mut v_f_2338_: *mut LeanObject,
    mut v_a_u2081_2339_: *mut LeanObject,
    mut v_a_u2082_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_2338_, v_a_u2081_2339_, v_a_u2082_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
    lean_dec(v___y_2351_);
    lean_dec_ref(v___y_2350_);
    lean_dec(v___y_2349_);
    lean_dec_ref(v___y_2348_);
    lean_dec(v___y_2347_);
    lean_dec_ref(v___y_2346_);
    lean_dec(v___y_2345_);
    lean_dec_ref(v___y_2344_);
    lean_dec(v___y_2343_);
    lean_dec(v___y_2342_);
    lean_dec_ref(v___y_2341_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(
    mut v_f_2354_: *mut LeanObject,
    mut v_a_u2081_2355_: *mut LeanObject,
    mut v_a_u2082_2356_: *mut LeanObject,
    mut v_a_u2083_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2370_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_2354_, v_a_u2081_2355_, v_a_u2082_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
    if lean_obj_tag(v___x_2370_) == 0 {
        let mut v_a_2371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
        v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
        lean_inc(v_a_2371_);
        lean_dec_ref_known(v___x_2370_, 1);
        v___x_2372_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_2371_, v_a_u2083_2357_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
        return v___x_2372_;
    } else {
        lean_dec_ref(v_a_u2083_2357_);
        return v___x_2370_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1___boxed(
    mut v_f_2373_: *mut LeanObject,
    mut v_a_u2081_2374_: *mut LeanObject,
    mut v_a_u2082_2375_: *mut LeanObject,
    mut v_a_u2083_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v_f_2373_, v_a_u2081_2374_, v_a_u2082_2375_, v_a_u2083_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
    lean_dec(v___y_2387_);
    lean_dec_ref(v___y_2386_);
    lean_dec(v___y_2385_);
    lean_dec_ref(v___y_2384_);
    lean_dec(v___y_2383_);
    lean_dec_ref(v___y_2382_);
    lean_dec(v___y_2381_);
    lean_dec_ref(v___y_2380_);
    lean_dec(v___y_2379_);
    lean_dec(v___y_2378_);
    lean_dec_ref(v___y_2377_);
    return v_res_2389_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2391_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0;
    v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(
    mut v_head_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u8 = 0;
    let mut v_arg_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v_arg_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v_arg_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_a_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v_a_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v_a_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_head_2402_);
                v___x_2415_ = l_Lean_MVarId_getType(
                    v_head_2402_,
                    v___y_2410_,
                    v___y_2411_,
                    v___y_2412_,
                    v___y_2413_,
                );
                if lean_obj_tag(v___x_2415_) == 0 {
                    v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
                    lean_inc_n(v_a_2416_, 2);
                    lean_dec_ref_known(v___x_2415_, 1);
                    v___x_2433_ = l_Lean_Expr_cleanupAnnotations(v_a_2416_);
                    v___x_2434_ = l_Lean_Expr_isApp(v___x_2433_);
                    if v___x_2434_ == 0 {
                        lean_dec_ref(v___x_2433_);
                        lean_dec(v_head_2402_);
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
                        v_arg_2435_ = lean_ctor_get(v___x_2433_, 1);
                        lean_inc_ref(v_arg_2435_);
                        v___x_2436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2433_);
                        v___x_2437_ = l_Lean_Expr_isApp(v___x_2436_);
                        if v___x_2437_ == 0 {
                            lean_dec_ref(v___x_2436_);
                            lean_dec_ref(v_arg_2435_);
                            lean_dec(v_head_2402_);
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
                            v_arg_2438_ = lean_ctor_get(v___x_2436_, 1);
                            lean_inc_ref(v_arg_2438_);
                            v___x_2439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2436_);
                            v___x_2440_ = l_Lean_Expr_isApp(v___x_2439_);
                            if v___x_2440_ == 0 {
                                lean_dec_ref(v___x_2439_);
                                lean_dec_ref(v_arg_2438_);
                                lean_dec_ref(v_arg_2435_);
                                lean_dec(v_head_2402_);
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
                                v_arg_2441_ = lean_ctor_get(v___x_2439_, 1);
                                lean_inc_ref(v_arg_2441_);
                                v___x_2442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2439_);
                                v___x_2443_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6;
                                v___x_2444_ = l_Lean_Expr_isConstOf(v___x_2442_, v___x_2443_);
                                if v___x_2444_ == 0 {
                                    lean_dec_ref(v___x_2442_);
                                    lean_dec_ref(v_arg_2441_);
                                    lean_dec_ref(v_arg_2438_);
                                    lean_dec_ref(v_arg_2435_);
                                    lean_dec(v_head_2402_);
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
                                    lean_dec(v_a_2416_);
                                    v___x_2445_ = l_Lean_Meta_Sym_unfoldReducible(
                                        v_arg_2441_,
                                        v___y_2410_,
                                        v___y_2411_,
                                        v___y_2412_,
                                        v___y_2413_,
                                    );
                                    if lean_obj_tag(v___x_2445_) == 0 {
                                        v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
                                        lean_inc(v_a_2446_);
                                        lean_dec_ref_known(v___x_2445_, 1);
                                        v___x_2447_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                            v_a_2446_,
                                            v___y_2409_,
                                        );
                                        if lean_obj_tag(v___x_2447_) == 0 {
                                            v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
                                            lean_inc(v_a_2448_);
                                            lean_dec_ref_known(v___x_2447_, 1);
                                            v___x_2449_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2442_, v_a_2448_, v_arg_2438_, v_arg_2435_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
                                            if lean_obj_tag(v___x_2449_) == 0 {
                                                v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
                                                lean_inc(v_a_2450_);
                                                lean_dec_ref_known(v___x_2449_, 1);
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
                                                lean_dec(v_head_2402_);
                                                v_a_2452_ = lean_ctor_get(v___x_2449_, 0);
                                                v_isSharedCheck_2459_ =
                                                    (!lean_is_exclusive(v___x_2449_)) as u8;
                                                if v_isSharedCheck_2459_ == 0 {
                                                    v___x_2454_ = v___x_2449_;
                                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2452_);
                                                    lean_dec(v___x_2449_);
                                                    v___x_2454_ = lean_box(0);
                                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2442_);
                                            lean_dec_ref(v_arg_2438_);
                                            lean_dec_ref(v_arg_2435_);
                                            lean_dec(v_head_2402_);
                                            v_a_2460_ = lean_ctor_get(v___x_2447_, 0);
                                            v_isSharedCheck_2467_ =
                                                (!lean_is_exclusive(v___x_2447_)) as u8;
                                            if v_isSharedCheck_2467_ == 0 {
                                                v___x_2462_ = v___x_2447_;
                                                v_isShared_2463_ = v_isSharedCheck_2467_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2460_);
                                                lean_dec(v___x_2447_);
                                                v___x_2462_ = lean_box(0);
                                                v_isShared_2463_ = v_isSharedCheck_2467_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_2442_);
                                        lean_dec_ref(v_arg_2438_);
                                        lean_dec_ref(v_arg_2435_);
                                        lean_dec(v_head_2402_);
                                        v_a_2468_ = lean_ctor_get(v___x_2445_, 0);
                                        v_isSharedCheck_2475_ =
                                            (!lean_is_exclusive(v___x_2445_)) as u8;
                                        if v_isSharedCheck_2475_ == 0 {
                                            v___x_2470_ = v___x_2445_;
                                            v_isShared_2471_ = v_isSharedCheck_2475_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2468_);
                                            lean_dec(v___x_2445_);
                                            v___x_2470_ = lean_box(0);
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
                    lean_dec(v_head_2402_);
                    v_a_2476_ = lean_ctor_get(v___x_2415_, 0);
                    v_isSharedCheck_2483_ = (!lean_is_exclusive(v___x_2415_)) as u8;
                    if v_isSharedCheck_2483_ == 0 {
                        v___x_2478_ = v___x_2415_;
                        v_isShared_2479_ = v_isSharedCheck_2483_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2476_);
                        lean_dec(v___x_2415_);
                        v___x_2478_ = lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2483_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1,
                );
                v___x_2430_ = l_Lean_MessageData_ofExpr(v_a_2416_);
                v___x_2431_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2431_, 0, v___x_2429_);
                lean_ctor_set(v___x_2431_, 1, v___x_2430_);
                v___x_2432_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2431_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
                return v___x_2432_;
            }
            2 => {
                if v_isShared_2455_ == 0 {
                    v___x_2457_ = v___x_2454_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
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
                    v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
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
                    v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
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
                    v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
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
    mut v_head_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2497_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2495_);
    lean_dec_ref(v___y_2494_);
    lean_dec(v___y_2493_);
    lean_dec_ref(v___y_2492_);
    lean_dec(v___y_2491_);
    lean_dec_ref(v___y_2490_);
    lean_dec(v___y_2489_);
    lean_dec_ref(v___y_2488_);
    lean_dec(v___y_2487_);
    lean_dec(v___y_2486_);
    lean_dec_ref(v___y_2485_);
    return v_res_2497_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2499_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0;
    v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
    return v___x_2500_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = 0;
    v___x_2509_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4;
    v___x_2510_ = l_Lean_MessageData_ofConstName(v___x_2509_, v___x_2508_);
    return v___x_2510_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5,
    );
    v___x_2512_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1,
    );
    v___x_2513_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2513_, 0, v___x_2512_);
    lean_ctor_set(v___x_2513_, 1, v___x_2511_);
    return v___x_2513_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8()
-> *mut LeanObject {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7;
    v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
    return v___x_2516_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9()
-> *mut LeanObject {
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    v___x_2517_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_2518_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6,
    );
    v___x_2519_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    lean_ctor_set(v___x_2519_, 1, v___x_2517_);
    return v___x_2519_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11()
-> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10;
    v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
    return v___x_2522_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(
    mut v_goal_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tripleOfEntailsWPRule_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tripleOfEntailsWPRule_2536_ = lean_ctor_get(v___y_2524_, 14);
                v___x_2537_ = lean_box(0);
                lean_inc(v_goal_2523_);
                lean_inc_ref(v_tripleOfEntailsWPRule_2536_);
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
                if lean_obj_tag(v___x_2538_) == 0 {
                    v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
                    lean_inc(v_a_2539_);
                    lean_dec_ref_known(v___x_2538_, 1);
                    if lean_obj_tag(v_a_2539_) == 1 {
                        v_mvarIds_2558_ = lean_ctor_get(v_a_2539_, 0);
                        lean_inc(v_mvarIds_2558_);
                        lean_dec_ref_known(v_a_2539_, 1);
                        if lean_obj_tag(v_mvarIds_2558_) == 1 {
                            v_tail_2559_ = lean_ctor_get(v_mvarIds_2558_, 1);
                            if lean_obj_tag(v_tail_2559_) == 0 {
                                lean_dec(v_goal_2523_);
                                v_head_2560_ = lean_ctor_get(v_mvarIds_2558_, 0);
                                lean_inc_n(v_head_2560_, 2);
                                lean_dec_ref_known(v_mvarIds_2558_, 2);
                                v___f_2561_ = lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    1,
                                );
                                lean_closure_set(v___f_2561_, 0, v_head_2560_);
                                v___x_2562_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_2560_, v___f_2561_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
                                return v___x_2562_;
                            } else {
                                lean_dec_ref_known(v_mvarIds_2558_, 2);
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
                            lean_dec(v_mvarIds_2558_);
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
                        lean_dec(v_a_2539_);
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
                    lean_dec(v_goal_2523_);
                    v_a_2563_ = lean_ctor_get(v___x_2538_, 0);
                    v_isSharedCheck_2570_ = (!lean_is_exclusive(v___x_2538_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2565_ = v___x_2538_;
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2563_);
                        lean_dec(v___x_2538_);
                        v___x_2565_ = lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2552_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9,
                );
                v___x_2553_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2553_, 0, v_goal_2523_);
                v___x_2554_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2554_, 0, v___x_2552_);
                lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                v___x_2555_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11,
                );
                v___x_2556_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2556_, 0, v___x_2554_);
                lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                v___x_2557_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2556_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
                return v___x_2557_;
            }
            2 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
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
    mut v_goal_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
    mut v___y_2575_: *mut LeanObject,
    mut v___y_2576_: *mut LeanObject,
    mut v___y_2577_: *mut LeanObject,
    mut v___y_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
    mut v___y_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2584_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2582_);
    lean_dec_ref(v___y_2581_);
    lean_dec(v___y_2580_);
    lean_dec_ref(v___y_2579_);
    lean_dec(v___y_2578_);
    lean_dec_ref(v___y_2577_);
    lean_dec(v___y_2576_);
    lean_dec_ref(v___y_2575_);
    lean_dec(v___y_2574_);
    lean_dec(v___y_2573_);
    lean_dec_ref(v___y_2572_);
    return v_res_2584_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(
    mut v_goal_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_2585_);
    v___f_2598_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed as *mut core::ffi::c_void,
        13,
        1,
    );
    lean_closure_set(v___f_2598_, 0, v_goal_2585_);
    v___x_2599_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_2585_, v___f_2598_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
    return v___x_2599_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___boxed(
    mut v_goal_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_a_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2613_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2611_);
    lean_dec_ref(v_a_2610_);
    lean_dec(v_a_2609_);
    lean_dec_ref(v_a_2608_);
    lean_dec(v_a_2607_);
    lean_dec_ref(v_a_2606_);
    lean_dec(v_a_2605_);
    lean_dec_ref(v_a_2604_);
    lean_dec(v_a_2603_);
    lean_dec(v_a_2602_);
    lean_dec_ref(v_a_2601_);
    return v_res_2613_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(
    mut v_00_u03b1_2614_: *mut LeanObject,
    mut v_msg_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2629_: *mut LeanObject,
    mut v_msg_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
    mut v___y_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2643_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2641_);
    lean_dec_ref(v___y_2640_);
    lean_dec(v___y_2639_);
    lean_dec_ref(v___y_2638_);
    lean_dec(v___y_2637_);
    lean_dec_ref(v___y_2636_);
    lean_dec(v___y_2635_);
    lean_dec_ref(v___y_2634_);
    lean_dec(v___y_2633_);
    lean_dec(v___y_2632_);
    lean_dec_ref(v___y_2631_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(
    mut v_f_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
    mut v___y_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2644_, v_a_2645_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___boxed(
    mut v_f_2659_: *mut LeanObject,
    mut v_a_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
    mut v___y_2669_: *mut LeanObject,
    mut v___y_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(v_f_2659_, v_a_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
    lean_dec(v___y_2671_);
    lean_dec_ref(v___y_2670_);
    lean_dec(v___y_2669_);
    lean_dec_ref(v___y_2668_);
    lean_dec(v___y_2667_);
    lean_dec_ref(v___y_2666_);
    lean_dec(v___y_2665_);
    lean_dec_ref(v___y_2664_);
    lean_dec(v___y_2663_);
    lean_dec(v___y_2662_);
    lean_dec_ref(v___y_2661_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(
    mut v_00___2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
    mut v___y_2679_: *mut LeanObject,
    mut v___y_2680_: *mut LeanObject,
    mut v___y_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    v___x_2687_ = lean_box(0);
    v___x_2688_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2688_, 0, v___x_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed(
    mut v_00___2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2702_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2700_);
    lean_dec_ref(v___y_2699_);
    lean_dec(v___y_2698_);
    lean_dec_ref(v___y_2697_);
    lean_dec(v___y_2696_);
    lean_dec_ref(v___y_2695_);
    lean_dec(v___y_2694_);
    lean_dec_ref(v___y_2693_);
    lean_dec(v___y_2692_);
    lean_dec(v___y_2691_);
    lean_dec_ref(v___y_2690_);
    return v_res_2702_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(
    mut v_goal_2709_: *mut LeanObject,
    mut v___f_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v_arg_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: u8 = 0;
    let mut v_arg_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v_arg_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsPureRule_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsFalseRule_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v___y_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsFalseRule_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_mvarIds_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_a_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_a_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_a_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_2709_);
                v___x_2723_ = l_Lean_MVarId_getType(
                    v_goal_2709_,
                    v___y_2718_,
                    v___y_2719_,
                    v___y_2720_,
                    v___y_2721_,
                );
                if lean_obj_tag(v___x_2723_) == 0 {
                    v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
                    v_isSharedCheck_2893_ = (!lean_is_exclusive(v___x_2723_)) as u8;
                    if v_isSharedCheck_2893_ == 0 {
                        v___x_2726_ = v___x_2723_;
                        v_isShared_2727_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2724_);
                        lean_dec(v___x_2723_);
                        v___x_2726_ = lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_2710_);
                    lean_dec(v_goal_2709_);
                    v_a_2894_ = lean_ctor_get(v___x_2723_, 0);
                    v_isSharedCheck_2901_ = (!lean_is_exclusive(v___x_2723_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v___x_2723_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_2894_);
                        lean_dec(v___x_2723_);
                        v___x_2896_ = lean_box(0);
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
                    lean_dec_ref(v___x_2733_);
                    lean_dec_ref(v___f_2710_);
                    lean_dec(v_goal_2709_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2735_ = lean_ctor_get(v___x_2733_, 1);
                    lean_inc_ref(v_arg_2735_);
                    v___x_2736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2733_);
                    v___x_2737_ = l_Lean_Expr_isApp(v___x_2736_);
                    if v___x_2737_ == 0 {
                        lean_dec_ref(v___x_2736_);
                        lean_dec_ref(v_arg_2735_);
                        lean_dec_ref(v___f_2710_);
                        lean_dec(v_goal_2709_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2738_ = lean_ctor_get(v___x_2736_, 1);
                        lean_inc_ref(v_arg_2738_);
                        v___x_2739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2736_);
                        v___x_2740_ = l_Lean_Expr_isApp(v___x_2739_);
                        if v___x_2740_ == 0 {
                            lean_dec_ref(v___x_2739_);
                            lean_dec_ref(v_arg_2738_);
                            lean_dec_ref(v_arg_2735_);
                            lean_dec_ref(v___f_2710_);
                            lean_dec(v_goal_2709_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2741_ = lean_ctor_get(v___x_2739_, 1);
                            lean_inc_ref(v_arg_2741_);
                            v___x_2742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2739_);
                            v___x_2743_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1;
                            v___x_2744_ = l_Lean_Expr_isConstOf(v___x_2742_, v___x_2743_);
                            if v___x_2744_ == 0 {
                                lean_dec_ref(v___x_2742_);
                                lean_dec_ref(v_arg_2741_);
                                lean_dec_ref(v_arg_2738_);
                                lean_dec_ref(v_arg_2735_);
                                lean_dec_ref(v___f_2710_);
                                lean_dec(v_goal_2709_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2726_);
                                v___x_2745_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                    v_arg_2738_,
                                    v___y_2716_,
                                    v___y_2717_,
                                    v___y_2718_,
                                    v___y_2719_,
                                    v___y_2720_,
                                    v___y_2721_,
                                );
                                if lean_obj_tag(v___x_2745_) == 0 {
                                    v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
                                    lean_inc(v_a_2746_);
                                    lean_dec_ref_known(v___x_2745_, 1);
                                    v___x_2747_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                        v_arg_2735_,
                                        v___y_2716_,
                                        v___y_2717_,
                                        v___y_2718_,
                                        v___y_2719_,
                                        v___y_2720_,
                                        v___y_2721_,
                                    );
                                    if lean_obj_tag(v___x_2747_) == 0 {
                                        v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
                                        lean_inc(v_a_2748_);
                                        lean_dec_ref_known(v___x_2747_, 1);
                                        v___x_2749_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2742_, v_arg_2741_, v_a_2746_, v_a_2748_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
                                        if lean_obj_tag(v___x_2749_) == 0 {
                                            v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
                                            lean_inc(v_a_2750_);
                                            lean_dec_ref_known(v___x_2749_, 1);
                                            v___x_2751_ = l_Lean_MVarId_replaceTargetDefEq(
                                                v_goal_2709_,
                                                v_a_2750_,
                                                v___y_2718_,
                                                v___y_2719_,
                                                v___y_2720_,
                                                v___y_2721_,
                                            );
                                            if lean_obj_tag(v___x_2751_) == 0 {
                                                v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
                                                v_isSharedCheck_2860_ =
                                                    (!lean_is_exclusive(v___x_2751_)) as u8;
                                                if v_isSharedCheck_2860_ == 0 {
                                                    v___x_2754_ = v___x_2751_;
                                                    v_isShared_2755_ = v_isSharedCheck_2860_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2752_);
                                                    lean_dec(v___x_2751_);
                                                    v___x_2754_ = lean_box(0);
                                                    v_isShared_2755_ = v_isSharedCheck_2860_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v___f_2710_);
                                                v_a_2861_ = lean_ctor_get(v___x_2751_, 0);
                                                v_isSharedCheck_2868_ =
                                                    (!lean_is_exclusive(v___x_2751_)) as u8;
                                                if v_isSharedCheck_2868_ == 0 {
                                                    v___x_2863_ = v___x_2751_;
                                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2861_);
                                                    lean_dec(v___x_2751_);
                                                    v___x_2863_ = lean_box(0);
                                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___f_2710_);
                                            lean_dec(v_goal_2709_);
                                            v_a_2869_ = lean_ctor_get(v___x_2749_, 0);
                                            v_isSharedCheck_2876_ =
                                                (!lean_is_exclusive(v___x_2749_)) as u8;
                                            if v_isSharedCheck_2876_ == 0 {
                                                v___x_2871_ = v___x_2749_;
                                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                                state = 20;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2869_);
                                                lean_dec(v___x_2749_);
                                                v___x_2871_ = lean_box(0);
                                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2746_);
                                        lean_dec_ref(v___x_2742_);
                                        lean_dec_ref(v_arg_2741_);
                                        lean_dec_ref(v___f_2710_);
                                        lean_dec(v_goal_2709_);
                                        v_a_2877_ = lean_ctor_get(v___x_2747_, 0);
                                        v_isSharedCheck_2884_ =
                                            (!lean_is_exclusive(v___x_2747_)) as u8;
                                        if v_isSharedCheck_2884_ == 0 {
                                            v___x_2879_ = v___x_2747_;
                                            v_isShared_2880_ = v_isSharedCheck_2884_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2877_);
                                            lean_dec(v___x_2747_);
                                            v___x_2879_ = lean_box(0);
                                            v_isShared_2880_ = v_isSharedCheck_2884_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_2742_);
                                    lean_dec_ref(v_arg_2741_);
                                    lean_dec_ref(v_arg_2735_);
                                    lean_dec_ref(v___f_2710_);
                                    lean_dec(v_goal_2709_);
                                    v_a_2885_ = lean_ctor_get(v___x_2745_, 0);
                                    v_isSharedCheck_2892_ = (!lean_is_exclusive(v___x_2745_)) as u8;
                                    if v_isSharedCheck_2892_ == 0 {
                                        v___x_2887_ = v___x_2745_;
                                        v_isShared_2888_ = v_isSharedCheck_2892_;
                                        state = 24;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2885_);
                                        lean_dec(v___x_2745_);
                                        v___x_2887_ = lean_box(0);
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
                v___x_2729_ = lean_box(0);
                if v_isShared_2727_ == 0 {
                    lean_ctor_set(v___x_2726_, 0, v___x_2729_);
                    v___x_2731_ = v___x_2726_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2731_;
            }
            4 => {
                v_exceptCondsEntailsRflRule_2761_ = lean_ctor_get(v___y_2711_, 10);
                v_exceptCondsEntailsPureRule_2762_ = lean_ctor_get(v___y_2711_, 11);
                v_exceptCondsEntailsFalseRule_2763_ = lean_ctor_get(v___y_2711_, 12);
                v_exceptCondsEntailsTrueRule_2764_ = lean_ctor_get(v___y_2711_, 13);
                v___x_2765_ = lean_box(0);
                lean_inc(v_a_2752_);
                lean_inc_ref(v_exceptCondsEntailsPureRule_2762_);
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
                if lean_obj_tag(v___x_2819_) == 0 {
                    v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
                    lean_inc(v_a_2820_);
                    lean_dec_ref_known(v___x_2819_, 1);
                    if lean_obj_tag(v_a_2820_) == 1 {
                        v_mvarIds_2849_ = lean_ctor_get(v_a_2820_, 0);
                        lean_inc(v_mvarIds_2849_);
                        lean_dec_ref_known(v_a_2820_, 1);
                        if lean_obj_tag(v_mvarIds_2849_) == 0 {
                            lean_del_object(v___x_2754_);
                            lean_dec(v_a_2752_);
                            v___x_2850_ = lean_box(0);
                            lean_inc(v___y_2721_);
                            lean_inc_ref(v___y_2720_);
                            lean_inc(v___y_2719_);
                            lean_inc_ref(v___y_2718_);
                            lean_inc(v___y_2717_);
                            lean_inc_ref(v___y_2716_);
                            lean_inc(v___y_2715_);
                            lean_inc_ref(v___y_2714_);
                            lean_inc(v___y_2713_);
                            lean_inc(v___y_2712_);
                            lean_inc_ref(v___y_2711_);
                            v___x_2851_ = lean_apply_13(
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
                                lean_box(0),
                            );
                            return v___x_2851_;
                        } else {
                            lean_dec(v_mvarIds_2849_);
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
                        lean_dec(v_a_2820_);
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
                    lean_del_object(v___x_2754_);
                    lean_dec(v_a_2752_);
                    lean_dec_ref(v___f_2710_);
                    v_a_2852_ = lean_ctor_get(v___x_2819_, 0);
                    v_isSharedCheck_2859_ = (!lean_is_exclusive(v___x_2819_)) as u8;
                    if v_isSharedCheck_2859_ == 0 {
                        v___x_2854_ = v___x_2819_;
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2852_);
                        lean_dec(v___x_2819_);
                        v___x_2854_ = lean_box(0);
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 16;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2757_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2757_, 0, v_a_2752_);
                if v_isShared_2755_ == 0 {
                    lean_ctor_set(v___x_2754_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2754_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2759_;
            }
            7 => {
                lean_inc(v_a_2752_);
                lean_inc_ref(v_exceptCondsEntailsRflRule_2768_);
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
                if lean_obj_tag(v___x_2779_) == 0 {
                    v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
                    lean_inc(v_a_2780_);
                    lean_dec_ref_known(v___x_2779_, 1);
                    if lean_obj_tag(v_a_2780_) == 1 {
                        v_mvarIds_2781_ = lean_ctor_get(v_a_2780_, 0);
                        lean_inc(v_mvarIds_2781_);
                        lean_dec_ref_known(v_a_2780_, 1);
                        if lean_obj_tag(v_mvarIds_2781_) == 0 {
                            lean_del_object(v___x_2754_);
                            lean_dec(v_a_2752_);
                            v___x_2782_ = lean_box(0);
                            lean_inc(v___y_2778_);
                            lean_inc_ref(v___y_2777_);
                            lean_inc(v___y_2776_);
                            lean_inc_ref(v___y_2775_);
                            lean_inc(v___y_2774_);
                            lean_inc_ref(v___y_2773_);
                            lean_inc(v___y_2772_);
                            lean_inc_ref(v___y_2771_);
                            lean_inc(v___y_2770_);
                            lean_inc(v___y_2769_);
                            lean_inc_ref(v___y_2767_);
                            v___x_2783_ = lean_apply_13(
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
                                lean_box(0),
                            );
                            return v___x_2783_;
                        } else {
                            lean_dec(v_mvarIds_2781_);
                            lean_dec_ref(v___f_2710_);
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2780_);
                        lean_dec_ref(v___f_2710_);
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2754_);
                    lean_dec(v_a_2752_);
                    lean_dec_ref(v___f_2710_);
                    v_a_2784_ = lean_ctor_get(v___x_2779_, 0);
                    v_isSharedCheck_2791_ = (!lean_is_exclusive(v___x_2779_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v___x_2786_ = v___x_2779_;
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2784_);
                        lean_dec(v___x_2779_);
                        v___x_2786_ = lean_box(0);
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
                    v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2789_;
            }
            10 => {
                lean_inc(v_a_2752_);
                lean_inc_ref(v_exceptCondsEntailsTrueRule_2795_);
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
                if lean_obj_tag(v___x_2806_) == 0 {
                    v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
                    lean_inc(v_a_2807_);
                    lean_dec_ref_known(v___x_2806_, 1);
                    if lean_obj_tag(v_a_2807_) == 1 {
                        v_mvarIds_2808_ = lean_ctor_get(v_a_2807_, 0);
                        lean_inc(v_mvarIds_2808_);
                        lean_dec_ref_known(v_a_2807_, 1);
                        if lean_obj_tag(v_mvarIds_2808_) == 0 {
                            lean_del_object(v___x_2754_);
                            lean_dec(v_a_2752_);
                            v___x_2809_ = lean_box(0);
                            lean_inc(v___y_2805_);
                            lean_inc_ref(v___y_2804_);
                            lean_inc(v___y_2803_);
                            lean_inc_ref(v___y_2802_);
                            lean_inc(v___y_2801_);
                            lean_inc_ref(v___y_2800_);
                            lean_inc(v___y_2799_);
                            lean_inc_ref(v___y_2798_);
                            lean_inc(v___y_2797_);
                            lean_inc(v___y_2796_);
                            lean_inc_ref(v___y_2793_);
                            v___x_2810_ = lean_apply_13(
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
                                lean_box(0),
                            );
                            return v___x_2810_;
                        } else {
                            lean_dec(v_mvarIds_2808_);
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
                        lean_dec(v_a_2807_);
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
                    lean_del_object(v___x_2754_);
                    lean_dec(v_a_2752_);
                    lean_dec_ref(v___f_2710_);
                    v_a_2811_ = lean_ctor_get(v___x_2806_, 0);
                    v_isSharedCheck_2818_ = (!lean_is_exclusive(v___x_2806_)) as u8;
                    if v_isSharedCheck_2818_ == 0 {
                        v___x_2813_ = v___x_2806_;
                        v_isShared_2814_ = v_isSharedCheck_2818_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2811_);
                        lean_dec(v___x_2806_);
                        v___x_2813_ = lean_box(0);
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
                    v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2816_;
            }
            13 => {
                lean_inc(v_a_2752_);
                lean_inc_ref(v_exceptCondsEntailsFalseRule_2824_);
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
                if lean_obj_tag(v___x_2836_) == 0 {
                    v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
                    lean_inc(v_a_2837_);
                    lean_dec_ref_known(v___x_2836_, 1);
                    if lean_obj_tag(v_a_2837_) == 1 {
                        v_mvarIds_2838_ = lean_ctor_get(v_a_2837_, 0);
                        lean_inc(v_mvarIds_2838_);
                        lean_dec_ref_known(v_a_2837_, 1);
                        if lean_obj_tag(v_mvarIds_2838_) == 0 {
                            lean_del_object(v___x_2754_);
                            lean_dec(v_a_2752_);
                            v___x_2839_ = lean_box(0);
                            lean_inc(v___y_2835_);
                            lean_inc_ref(v___y_2834_);
                            lean_inc(v___y_2833_);
                            lean_inc_ref(v___y_2832_);
                            lean_inc(v___y_2831_);
                            lean_inc_ref(v___y_2830_);
                            lean_inc(v___y_2829_);
                            lean_inc_ref(v___y_2828_);
                            lean_inc(v___y_2827_);
                            lean_inc(v___y_2826_);
                            lean_inc_ref(v___y_2822_);
                            v___x_2840_ = lean_apply_13(
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
                                lean_box(0),
                            );
                            return v___x_2840_;
                        } else {
                            lean_dec(v_mvarIds_2838_);
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
                        lean_dec(v_a_2837_);
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
                    lean_del_object(v___x_2754_);
                    lean_dec(v_a_2752_);
                    lean_dec_ref(v___f_2710_);
                    v_a_2841_ = lean_ctor_get(v___x_2836_, 0);
                    v_isSharedCheck_2848_ = (!lean_is_exclusive(v___x_2836_)) as u8;
                    if v_isSharedCheck_2848_ == 0 {
                        v___x_2843_ = v___x_2836_;
                        v_isShared_2844_ = v_isSharedCheck_2848_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2841_);
                        lean_dec(v___x_2836_);
                        v___x_2843_ = lean_box(0);
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
                    v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
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
                    v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
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
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
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
                    v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
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
                    v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
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
                    v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
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
                    v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
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
    mut v_goal_2902_: *mut LeanObject,
    mut v___f_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2916_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2914_);
    lean_dec_ref(v___y_2913_);
    lean_dec(v___y_2912_);
    lean_dec_ref(v___y_2911_);
    lean_dec(v___y_2910_);
    lean_dec_ref(v___y_2909_);
    lean_dec(v___y_2908_);
    lean_dec_ref(v___y_2907_);
    lean_dec(v___y_2906_);
    lean_dec(v___y_2905_);
    lean_dec_ref(v___y_2904_);
    return v_res_2916_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(
    mut v_goal_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v___f_2931_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0;
    lean_inc(v_goal_2918_);
    v___f_2932_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed
            as *mut core::ffi::c_void,
        14,
        2,
    );
    lean_closure_set(v___f_2932_, 0, v_goal_2918_);
    lean_closure_set(v___f_2932_, 1, v___f_2931_);
    v___x_2933_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_2918_, v___f_2932_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
    return v___x_2933_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed(
    mut v_goal_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2947_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2945_);
    lean_dec_ref(v_a_2944_);
    lean_dec(v_a_2943_);
    lean_dec_ref(v_a_2942_);
    lean_dec(v_a_2941_);
    lean_dec_ref(v_a_2940_);
    lean_dec(v_a_2939_);
    lean_dec_ref(v_a_2938_);
    lean_dec(v_a_2937_);
    lean_dec(v_a_2936_);
    lean_dec_ref(v_a_2935_);
    return v_res_2947_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0;
    v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
    return v___x_2950_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    v___x_2952_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2;
    v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
    return v___x_2953_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(
    mut v_head_2954_: *mut LeanObject,
    mut v___x_2955_: *mut LeanObject,
    mut v___x_2956_: *mut LeanObject,
    mut v___x_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
    mut v___y_2967_: *mut LeanObject,
    mut v___y_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2984_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_arg_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u8 = 0;
    let mut v_arg_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v_arg_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_a_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_a_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_a_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_head_2954_);
                v___x_2970_ = l_Lean_MVarId_getType(
                    v_head_2954_,
                    v___y_2965_,
                    v___y_2966_,
                    v___y_2967_,
                    v___y_2968_,
                );
                if lean_obj_tag(v___x_2970_) == 0 {
                    v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
                    lean_inc(v_a_2971_);
                    lean_dec_ref_known(v___x_2970_, 1);
                    if lean_obj_tag(v_a_2971_) == 7 {
                        v_binderName_2981_ = lean_ctor_get(v_a_2971_, 0);
                        v_binderType_2982_ = lean_ctor_get(v_a_2971_, 1);
                        v_body_2983_ = lean_ctor_get(v_a_2971_, 2);
                        v_binderInfo_2984_ = lean_ctor_get_uint8(
                            v_a_2971_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_inc_ref(v_body_2983_);
                        v___x_2985_ = l_Lean_Expr_cleanupAnnotations(v_body_2983_);
                        v___x_2986_ = l_Lean_Expr_isApp(v___x_2985_);
                        if v___x_2986_ == 0 {
                            lean_dec_ref(v___x_2985_);
                            lean_dec_ref(v___x_2957_);
                            lean_dec_ref(v___x_2956_);
                            lean_dec_ref(v___x_2955_);
                            lean_dec(v_head_2954_);
                            v___y_2973_ = v___y_2965_;
                            v___y_2974_ = v___y_2966_;
                            v___y_2975_ = v___y_2967_;
                            v___y_2976_ = v___y_2968_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_2987_ = lean_ctor_get(v___x_2985_, 1);
                            lean_inc_ref(v_arg_2987_);
                            v___x_2988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2985_);
                            v___x_2989_ = l_Lean_Expr_isApp(v___x_2988_);
                            if v___x_2989_ == 0 {
                                lean_dec_ref(v___x_2988_);
                                lean_dec_ref(v_arg_2987_);
                                lean_dec_ref(v___x_2957_);
                                lean_dec_ref(v___x_2956_);
                                lean_dec_ref(v___x_2955_);
                                lean_dec(v_head_2954_);
                                v___y_2973_ = v___y_2965_;
                                v___y_2974_ = v___y_2966_;
                                v___y_2975_ = v___y_2967_;
                                v___y_2976_ = v___y_2968_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_2990_ = lean_ctor_get(v___x_2988_, 1);
                                lean_inc_ref(v_arg_2990_);
                                v___x_2991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2988_);
                                v___x_2992_ = l_Lean_Expr_isApp(v___x_2991_);
                                if v___x_2992_ == 0 {
                                    lean_dec_ref(v___x_2991_);
                                    lean_dec_ref(v_arg_2990_);
                                    lean_dec_ref(v_arg_2987_);
                                    lean_dec_ref(v___x_2957_);
                                    lean_dec_ref(v___x_2956_);
                                    lean_dec_ref(v___x_2955_);
                                    lean_dec(v_head_2954_);
                                    v___y_2973_ = v___y_2965_;
                                    v___y_2974_ = v___y_2966_;
                                    v___y_2975_ = v___y_2967_;
                                    v___y_2976_ = v___y_2968_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2993_ = lean_ctor_get(v___x_2991_, 1);
                                    lean_inc_ref(v_arg_2993_);
                                    v___x_2994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2991_);
                                    v___x_2995_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4;
                                    v___x_2996_ = l_Lean_Name_mkStr4(
                                        v___x_2955_,
                                        v___x_2956_,
                                        v___x_2995_,
                                        v___x_2957_,
                                    );
                                    v___x_2997_ = l_Lean_Expr_isConstOf(v___x_2994_, v___x_2996_);
                                    lean_dec(v___x_2996_);
                                    if v___x_2997_ == 0 {
                                        lean_dec_ref(v___x_2994_);
                                        lean_dec_ref(v_arg_2993_);
                                        lean_dec_ref(v_arg_2990_);
                                        lean_dec_ref(v_arg_2987_);
                                        lean_dec(v_head_2954_);
                                        v___y_2973_ = v___y_2965_;
                                        v___y_2974_ = v___y_2966_;
                                        v___y_2975_ = v___y_2967_;
                                        v___y_2976_ = v___y_2968_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc_ref(v_binderType_2982_);
                                        lean_inc(v_binderName_2981_);
                                        lean_dec_ref_known(v_a_2971_, 3);
                                        v___x_2998_ = l_Lean_Meta_Sym_unfoldReducible(
                                            v_arg_2993_,
                                            v___y_2965_,
                                            v___y_2966_,
                                            v___y_2967_,
                                            v___y_2968_,
                                        );
                                        if lean_obj_tag(v___x_2998_) == 0 {
                                            v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
                                            lean_inc(v_a_2999_);
                                            lean_dec_ref_known(v___x_2998_, 1);
                                            v___x_3000_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                                v_a_2999_,
                                                v___y_2964_,
                                            );
                                            if lean_obj_tag(v___x_3000_) == 0 {
                                                v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
                                                lean_inc(v_a_3001_);
                                                lean_dec_ref_known(v___x_3000_, 1);
                                                v___x_3002_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2994_, v_a_3001_, v_arg_2990_, v_arg_2987_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
                                                if lean_obj_tag(v___x_3002_) == 0 {
                                                    v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
                                                    lean_inc(v_a_3003_);
                                                    lean_dec_ref_known(v___x_3002_, 1);
                                                    v___x_3004_ = l_Lean_Expr_forallE___override(
                                                        v_binderName_2981_,
                                                        v_binderType_2982_,
                                                        v_a_3003_,
                                                        v_binderInfo_2984_,
                                                    );
                                                    v___x_3005_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3004_, v___y_2964_);
                                                    if lean_obj_tag(v___x_3005_) == 0 {
                                                        v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
                                                        lean_inc(v_a_3006_);
                                                        lean_dec_ref_known(v___x_3005_, 1);
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
                                                        lean_dec(v_head_2954_);
                                                        v_a_3008_ = lean_ctor_get(v___x_3005_, 0);
                                                        v_isSharedCheck_3015_ =
                                                            (!lean_is_exclusive(v___x_3005_)) as u8;
                                                        if v_isSharedCheck_3015_ == 0 {
                                                            v___x_3010_ = v___x_3005_;
                                                            v_isShared_3011_ =
                                                                v_isSharedCheck_3015_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3008_);
                                                            lean_dec(v___x_3005_);
                                                            v___x_3010_ = lean_box(0);
                                                            v_isShared_3011_ =
                                                                v_isSharedCheck_3015_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_binderType_2982_);
                                                    lean_dec(v_binderName_2981_);
                                                    lean_dec(v_head_2954_);
                                                    v_a_3016_ = lean_ctor_get(v___x_3002_, 0);
                                                    v_isSharedCheck_3023_ =
                                                        (!lean_is_exclusive(v___x_3002_)) as u8;
                                                    if v_isSharedCheck_3023_ == 0 {
                                                        v___x_3018_ = v___x_3002_;
                                                        v_isShared_3019_ = v_isSharedCheck_3023_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3016_);
                                                        lean_dec(v___x_3002_);
                                                        v___x_3018_ = lean_box(0);
                                                        v_isShared_3019_ = v_isSharedCheck_3023_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2994_);
                                                lean_dec_ref(v_arg_2990_);
                                                lean_dec_ref(v_arg_2987_);
                                                lean_dec_ref(v_binderType_2982_);
                                                lean_dec(v_binderName_2981_);
                                                lean_dec(v_head_2954_);
                                                v_a_3024_ = lean_ctor_get(v___x_3000_, 0);
                                                v_isSharedCheck_3031_ =
                                                    (!lean_is_exclusive(v___x_3000_)) as u8;
                                                if v_isSharedCheck_3031_ == 0 {
                                                    v___x_3026_ = v___x_3000_;
                                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3024_);
                                                    lean_dec(v___x_3000_);
                                                    v___x_3026_ = lean_box(0);
                                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2994_);
                                            lean_dec_ref(v_arg_2990_);
                                            lean_dec_ref(v_arg_2987_);
                                            lean_dec_ref(v_binderType_2982_);
                                            lean_dec(v_binderName_2981_);
                                            lean_dec(v_head_2954_);
                                            v_a_3032_ = lean_ctor_get(v___x_2998_, 0);
                                            v_isSharedCheck_3039_ =
                                                (!lean_is_exclusive(v___x_2998_)) as u8;
                                            if v_isSharedCheck_3039_ == 0 {
                                                v___x_3034_ = v___x_2998_;
                                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3032_);
                                                lean_dec(v___x_2998_);
                                                v___x_3034_ = lean_box(0);
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
                        lean_dec_ref(v___x_2957_);
                        lean_dec_ref(v___x_2956_);
                        lean_dec_ref(v___x_2955_);
                        lean_dec(v_head_2954_);
                        v___x_3040_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3);
                        v___x_3041_ = l_Lean_MessageData_ofExpr(v_a_2971_);
                        v___x_3042_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3042_, 0, v___x_3040_);
                        lean_ctor_set(v___x_3042_, 1, v___x_3041_);
                        v___x_3043_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3042_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
                        return v___x_3043_;
                    }
                } else {
                    lean_dec_ref(v___x_2957_);
                    lean_dec_ref(v___x_2956_);
                    lean_dec_ref(v___x_2955_);
                    lean_dec(v_head_2954_);
                    v_a_3044_ = lean_ctor_get(v___x_2970_, 0);
                    v_isSharedCheck_3051_ = (!lean_is_exclusive(v___x_2970_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v___x_3046_ = v___x_2970_;
                        v_isShared_3047_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3044_);
                        lean_dec(v___x_2970_);
                        v___x_3046_ = lean_box(0);
                        v_isShared_3047_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2977_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
                v___x_2978_ = l_Lean_MessageData_ofExpr(v_a_2971_);
                v___x_2979_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2979_, 0, v___x_2977_);
                lean_ctor_set(v___x_2979_, 1, v___x_2978_);
                v___x_2980_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2979_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
                return v___x_2980_;
            }
            2 => {
                if v_isShared_3011_ == 0 {
                    v___x_3013_ = v___x_3010_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
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
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
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
                    v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
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
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
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
                    v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
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
    mut v_head_3052_: *mut LeanObject,
    mut v___x_3053_: *mut LeanObject,
    mut v___x_3054_: *mut LeanObject,
    mut v___x_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3066_);
    lean_dec_ref(v___y_3065_);
    lean_dec(v___y_3064_);
    lean_dec_ref(v___y_3063_);
    lean_dec(v___y_3062_);
    lean_dec_ref(v___y_3061_);
    lean_dec(v___y_3060_);
    lean_dec_ref(v___y_3059_);
    lean_dec(v___y_3058_);
    lean_dec(v___y_3057_);
    lean_dec_ref(v___y_3056_);
    return v_res_3068_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    v___x_3075_ = 0;
    v___x_3076_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1;
    v___x_3077_ = l_Lean_MessageData_ofConstName(v___x_3076_, v___x_3075_);
    return v___x_3077_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    v___x_3078_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2,
    );
    v___x_3079_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1,
    );
    v___x_3080_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3080_, 0, v___x_3079_);
    lean_ctor_set(v___x_3080_, 1, v___x_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    v___x_3081_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3082_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3,
    );
    v___x_3083_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3083_, 0, v___x_3082_);
    lean_ctor_set(v___x_3083_, 1, v___x_3081_);
    return v___x_3083_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___x_3085_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5;
    v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(
    mut v_goal_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v_postCondEntailsRflRule_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postCondEntailsMkRule_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___y_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postCondEntailsMkRule_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_unused_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v_mvarIds_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v_a_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_a_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_3087_);
                v___x_3106_ = l_Lean_MVarId_getType(
                    v_goal_3087_,
                    v___y_3095_,
                    v___y_3096_,
                    v___y_3097_,
                    v___y_3098_,
                );
                if lean_obj_tag(v___x_3106_) == 0 {
                    v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3229_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v___x_3109_ = v___x_3106_;
                        v_isShared_3110_ = v_isSharedCheck_3229_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3107_);
                        lean_dec(v___x_3106_);
                        v___x_3109_ = lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3229_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_3087_);
                    v_a_3230_ = lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3237_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3237_ == 0 {
                        v___x_3232_ = v___x_3106_;
                        v_isShared_3233_ = v_isSharedCheck_3237_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3230_);
                        lean_dec(v___x_3106_);
                        v___x_3232_ = lean_box(0);
                        v_isShared_3233_ = v_isSharedCheck_3237_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3103_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3103_, 0, v___y_3101_);
                lean_ctor_set(v___x_3103_, 1, v___y_3102_);
                v___x_3104_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3104_, 0, v___x_3103_);
                v___x_3105_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3105_, 0, v___x_3104_);
                return v___x_3105_;
            }
            2 => {
                lean_inc(v_a_3107_);
                v___x_3127_ = l_Lean_Expr_cleanupAnnotations(v_a_3107_);
                v___x_3128_ = l_Lean_Expr_isApp(v___x_3127_);
                if v___x_3128_ == 0 {
                    lean_dec_ref(v___x_3127_);
                    lean_dec(v_a_3107_);
                    lean_dec(v_goal_3087_);
                    state = 3;
                    continue;
                } else {
                    v___x_3129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3127_);
                    v___x_3130_ = l_Lean_Expr_isApp(v___x_3129_);
                    if v___x_3130_ == 0 {
                        lean_dec_ref(v___x_3129_);
                        lean_dec(v_a_3107_);
                        lean_dec(v_goal_3087_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3129_);
                        v___x_3132_ = l_Lean_Expr_isApp(v___x_3131_);
                        if v___x_3132_ == 0 {
                            lean_dec_ref(v___x_3131_);
                            lean_dec(v_a_3107_);
                            lean_dec(v_goal_3087_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3131_);
                            v___x_3134_ = l_Lean_Expr_isApp(v___x_3133_);
                            if v___x_3134_ == 0 {
                                lean_dec_ref(v___x_3133_);
                                lean_dec(v_a_3107_);
                                lean_dec(v_goal_3087_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3133_);
                                v___x_3136_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2;
                                v___x_3137_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3;
                                v___x_3138_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5;
                                v___x_3139_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1;
                                v___x_3140_ = l_Lean_Expr_isConstOf(v___x_3135_, v___x_3139_);
                                lean_dec_ref(v___x_3135_);
                                if v___x_3140_ == 0 {
                                    lean_dec(v_a_3107_);
                                    lean_dec(v_goal_3087_);
                                    state = 3;
                                    continue;
                                } else {
                                    lean_del_object(v___x_3109_);
                                    v_postCondEntailsRflRule_3141_ = lean_ctor_get(v___y_3088_, 8);
                                    v_postCondEntailsMkRule_3142_ = lean_ctor_get(v___y_3088_, 9);
                                    v___x_3143_ = lean_box(0);
                                    lean_inc(v_goal_3087_);
                                    lean_inc_ref(v_postCondEntailsRflRule_3141_);
                                    v___x_3144_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_postCondEntailsRflRule_3141_, v_goal_3087_, v___x_3143_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
                                    if lean_obj_tag(v___x_3144_) == 0 {
                                        v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
                                        v_isSharedCheck_3220_ =
                                            (!lean_is_exclusive(v___x_3144_)) as u8;
                                        if v_isSharedCheck_3220_ == 0 {
                                            v___x_3147_ = v___x_3144_;
                                            v_isShared_3148_ = v_isSharedCheck_3220_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3145_);
                                            lean_dec(v___x_3144_);
                                            v___x_3147_ = lean_box(0);
                                            v_isShared_3148_ = v_isSharedCheck_3220_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3107_);
                                        lean_dec(v_goal_3087_);
                                        v_a_3221_ = lean_ctor_get(v___x_3144_, 0);
                                        v_isSharedCheck_3228_ =
                                            (!lean_is_exclusive(v___x_3144_)) as u8;
                                        if v_isSharedCheck_3228_ == 0 {
                                            v___x_3223_ = v___x_3144_;
                                            v_isShared_3224_ = v_isSharedCheck_3228_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3221_);
                                            lean_dec(v___x_3144_);
                                            v___x_3223_ = lean_box(0);
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
                v___x_3112_ = lean_box(0);
                if v_isShared_3110_ == 0 {
                    lean_ctor_set(v___x_3109_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3114_;
            }
            5 => {
                v___x_3121_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4);
                v___x_3122_ = l_Lean_MessageData_ofExpr(v_a_3107_);
                v___x_3123_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3123_, 0, v___x_3121_);
                lean_ctor_set(v___x_3123_, 1, v___x_3122_);
                v___x_3124_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6);
                v___x_3125_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3125_, 0, v___x_3123_);
                lean_ctor_set(v___x_3125_, 1, v___x_3124_);
                v___x_3126_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3125_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
                return v___x_3126_;
            }
            6 => {
                if lean_obj_tag(v_a_3145_) == 1 {
                    v_mvarIds_3209_ = lean_ctor_get(v_a_3145_, 0);
                    v_isSharedCheck_3219_ = (!lean_is_exclusive(v_a_3145_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v___x_3211_ = v_a_3145_;
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_mvarIds_3209_);
                        lean_dec(v_a_3145_);
                        v___x_3211_ = lean_box(0);
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3147_);
                    lean_dec(v_a_3145_);
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
                lean_inc_ref(v_postCondEntailsMkRule_3151_);
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
                if lean_obj_tag(v___x_3162_) == 0 {
                    v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
                    lean_inc(v_a_3163_);
                    lean_dec_ref_known(v___x_3162_, 1);
                    if lean_obj_tag(v_a_3163_) == 1 {
                        v_mvarIds_3164_ = lean_ctor_get(v_a_3163_, 0);
                        lean_inc(v_mvarIds_3164_);
                        lean_dec_ref_known(v_a_3163_, 1);
                        if lean_obj_tag(v_mvarIds_3164_) == 1 {
                            v_tail_3165_ = lean_ctor_get(v_mvarIds_3164_, 1);
                            lean_inc(v_tail_3165_);
                            if lean_obj_tag(v_tail_3165_) == 1 {
                                v_tail_3166_ = lean_ctor_get(v_tail_3165_, 1);
                                lean_inc(v_tail_3166_);
                                if lean_obj_tag(v_tail_3166_) == 0 {
                                    lean_dec(v_a_3107_);
                                    v_head_3167_ = lean_ctor_get(v_mvarIds_3164_, 0);
                                    lean_inc(v_head_3167_);
                                    lean_dec_ref_known(v_mvarIds_3164_, 2);
                                    v_head_3168_ = lean_ctor_get(v_tail_3165_, 0);
                                    v_isSharedCheck_3199_ =
                                        (!lean_is_exclusive(v_tail_3165_)) as u8;
                                    if v_isSharedCheck_3199_ == 0 {
                                        v_unused_3200_ = lean_ctor_get(v_tail_3165_, 1);
                                        lean_dec(v_unused_3200_);
                                        v___x_3170_ = v_tail_3165_;
                                        v_isShared_3171_ = v_isSharedCheck_3199_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_head_3168_);
                                        lean_dec(v_tail_3165_);
                                        v___x_3170_ = lean_box(0);
                                        v_isShared_3171_ = v_isSharedCheck_3199_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_tail_3165_, 2);
                                    lean_dec(v_tail_3166_);
                                    lean_dec_ref_known(v_mvarIds_3164_, 2);
                                    v___y_3117_ = v___y_3158_;
                                    v___y_3118_ = v___y_3159_;
                                    v___y_3119_ = v___y_3160_;
                                    v___y_3120_ = v___y_3161_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_tail_3165_);
                                lean_dec_ref_known(v_mvarIds_3164_, 2);
                                v___y_3117_ = v___y_3158_;
                                v___y_3118_ = v___y_3159_;
                                v___y_3119_ = v___y_3160_;
                                v___y_3120_ = v___y_3161_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarIds_3164_);
                            v___y_3117_ = v___y_3158_;
                            v___y_3118_ = v___y_3159_;
                            v___y_3119_ = v___y_3160_;
                            v___y_3120_ = v___y_3161_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3163_);
                        v___y_3117_ = v___y_3158_;
                        v___y_3118_ = v___y_3159_;
                        v___y_3119_ = v___y_3160_;
                        v___y_3120_ = v___y_3161_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3107_);
                    v_a_3201_ = lean_ctor_get(v___x_3162_, 0);
                    v_isSharedCheck_3208_ = (!lean_is_exclusive(v___x_3162_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3203_ = v___x_3162_;
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3201_);
                        lean_dec(v___x_3162_);
                        v___x_3203_ = lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                lean_inc(v_head_3168_);
                v___x_3172_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed
                        as *mut core::ffi::c_void,
                    13,
                    1,
                );
                lean_closure_set(v___x_3172_, 0, v_head_3168_);
                v___x_3173_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_3168_, v___x_3172_, v___y_3150_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
                if lean_obj_tag(v___x_3173_) == 0 {
                    v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
                    lean_inc(v_a_3174_);
                    lean_dec_ref_known(v___x_3173_, 1);
                    lean_inc(v_head_3167_);
                    v___f_3175_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed
                            as *mut core::ffi::c_void,
                        16,
                        4,
                    );
                    lean_closure_set(v___f_3175_, 0, v_head_3167_);
                    lean_closure_set(v___f_3175_, 1, v___x_3136_);
                    lean_closure_set(v___f_3175_, 2, v___x_3137_);
                    lean_closure_set(v___f_3175_, 3, v___x_3138_);
                    v___x_3176_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_3167_, v___f_3175_, v___y_3150_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
                    if lean_obj_tag(v___x_3176_) == 0 {
                        if lean_obj_tag(v_a_3174_) == 0 {
                            lean_del_object(v___x_3170_);
                            v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
                            lean_inc(v_a_3177_);
                            lean_dec_ref_known(v___x_3176_, 1);
                            v___y_3101_ = v_a_3177_;
                            v___y_3102_ = v_tail_3166_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3178_ = lean_ctor_get(v___x_3176_, 0);
                            lean_inc(v_a_3178_);
                            lean_dec_ref_known(v___x_3176_, 1);
                            v_val_3179_ = lean_ctor_get(v_a_3174_, 0);
                            lean_inc(v_val_3179_);
                            lean_dec_ref_known(v_a_3174_, 1);
                            if v_isShared_3171_ == 0 {
                                lean_ctor_set(v___x_3170_, 0, v_val_3179_);
                                v___x_3181_ = v___x_3170_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_val_3179_);
                                lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_tail_3166_);
                                v___x_3181_ = v_reuseFailAlloc_3182_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3174_);
                        lean_del_object(v___x_3170_);
                        v_a_3183_ = lean_ctor_get(v___x_3176_, 0);
                        v_isSharedCheck_3190_ = (!lean_is_exclusive(v___x_3176_)) as u8;
                        if v_isSharedCheck_3190_ == 0 {
                            v___x_3185_ = v___x_3176_;
                            v_isShared_3186_ = v_isSharedCheck_3190_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3183_);
                            lean_dec(v___x_3176_);
                            v___x_3185_ = lean_box(0);
                            v_isShared_3186_ = v_isSharedCheck_3190_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3170_);
                    lean_dec(v_head_3167_);
                    v_a_3191_ = lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3198_ = (!lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v___x_3193_ = v___x_3173_;
                        v_isShared_3194_ = v_isSharedCheck_3198_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3191_);
                        lean_dec(v___x_3173_);
                        v___x_3193_ = lean_box(0);
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
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
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
                    v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
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
                    v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3206_;
            }
            16 => {
                if lean_obj_tag(v_mvarIds_3209_) == 0 {
                    lean_dec(v_a_3107_);
                    lean_dec(v_goal_3087_);
                    if v_isShared_3212_ == 0 {
                        v___x_3214_ = v___x_3211_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_mvarIds_3209_);
                        v___x_3214_ = v_reuseFailAlloc_3218_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3211_);
                    lean_dec(v_mvarIds_3209_);
                    lean_del_object(v___x_3147_);
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
                    lean_ctor_set(v___x_3147_, 0, v___x_3214_);
                    v___x_3216_ = v___x_3147_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
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
                    v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
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
                    v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
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
    mut v_goal_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3251_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3249_);
    lean_dec_ref(v___y_3248_);
    lean_dec(v___y_3247_);
    lean_dec_ref(v___y_3246_);
    lean_dec(v___y_3245_);
    lean_dec_ref(v___y_3244_);
    lean_dec(v___y_3243_);
    lean_dec_ref(v___y_3242_);
    lean_dec(v___y_3241_);
    lean_dec(v___y_3240_);
    lean_dec_ref(v___y_3239_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(
    mut v_goal_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
    mut v_a_3256_: *mut LeanObject,
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_a_3263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_3252_);
    v___f_3265_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    lean_closure_set(v___f_3265_, 0, v_goal_3252_);
    v___x_3266_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_3252_, v___f_3265_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
    return v___x_3266_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___boxed(
    mut v_goal_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
    mut v_a_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3280_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3278_);
    lean_dec_ref(v_a_3277_);
    lean_dec(v_a_3276_);
    lean_dec_ref(v_a_3275_);
    lean_dec(v_a_3274_);
    lean_dec_ref(v_a_3273_);
    lean_dec(v_a_3272_);
    lean_dec_ref(v_a_3271_);
    lean_dec(v_a_3270_);
    lean_dec(v_a_3269_);
    lean_dec_ref(v_a_3268_);
    return v_res_3280_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1()
-> *mut LeanObject {
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0;
    v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
    return v___x_3283_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4()
-> *mut LeanObject {
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    v___x_3290_ = 0;
    v___x_3291_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3;
    v___x_3292_ = l_Lean_MessageData_ofConstName(v___x_3291_, v___x_3290_);
    return v___x_3292_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5()
-> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    v___x_3293_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4,
    );
    v___x_3294_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3295_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3295_, 0, v___x_3294_);
    lean_ctor_set(v___x_3295_, 1, v___x_3293_);
    return v___x_3295_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(
    mut v_goal_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_goal_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entailsConsIntroRule_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_applyPureConsEntailsLRule_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_applyPureConsEntailsRRule_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goal_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_mvarIds_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_a_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3378_: u8 = 0;
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v_a_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entailsConsIntroRule_3313_ = lean_ctor_get(v_a_3297_, 0);
                v_applyPureConsEntailsLRule_3314_ = lean_ctor_get(v_a_3297_, 3);
                v_applyPureConsEntailsRRule_3315_ = lean_ctor_get(v_a_3297_, 4);
                v___x_3316_ = lean_box(0);
                lean_inc_ref(v_entailsConsIntroRule_3313_);
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
                if lean_obj_tag(v___x_3317_) == 0 {
                    v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
                    v_isSharedCheck_3379_ = (!lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3379_ == 0 {
                        v___x_3320_ = v___x_3317_;
                        v_isShared_3321_ = v_isSharedCheck_3379_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3318_);
                        lean_dec(v___x_3317_);
                        v___x_3320_ = lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3379_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3380_ = lean_ctor_get(v___x_3317_, 0);
                    v_isSharedCheck_3387_ = (!lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v___x_3382_ = v___x_3317_;
                        v_isShared_3383_ = v_isSharedCheck_3387_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3380_);
                        lean_dec(v___x_3317_);
                        v___x_3382_ = lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3387_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3311_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3311_, 0, v_goal_3310_);
                v___x_3312_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3312_, 0, v___x_3311_);
                return v___x_3312_;
            }
            2 => {
                if lean_obj_tag(v_a_3318_) == 1 {
                    v_mvarIds_3326_ = lean_ctor_get(v_a_3318_, 0);
                    lean_inc(v_mvarIds_3326_);
                    lean_dec_ref_known(v_a_3318_, 1);
                    if lean_obj_tag(v_mvarIds_3326_) == 1 {
                        v_tail_3327_ = lean_ctor_get(v_mvarIds_3326_, 1);
                        if lean_obj_tag(v_tail_3327_) == 0 {
                            lean_del_object(v___x_3320_);
                            v_head_3328_ = lean_ctor_get(v_mvarIds_3326_, 0);
                            lean_inc(v_head_3328_);
                            lean_dec_ref_known(v_mvarIds_3326_, 2);
                            v___x_3329_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5);
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
                            if lean_obj_tag(v___x_3330_) == 0 {
                                v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
                                lean_inc_n(v_a_3331_, 2);
                                lean_dec_ref_known(v___x_3330_, 1);
                                lean_inc_ref(v_applyPureConsEntailsLRule_3314_);
                                v___x_3332_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_applyPureConsEntailsLRule_3314_, v_a_3331_, v___x_3316_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
                                if lean_obj_tag(v___x_3332_) == 0 {
                                    v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
                                    lean_inc(v_a_3333_);
                                    lean_dec_ref_known(v___x_3332_, 1);
                                    if lean_obj_tag(v_a_3333_) == 1 {
                                        v_mvarIds_3360_ = lean_ctor_get(v_a_3333_, 0);
                                        lean_inc(v_mvarIds_3360_);
                                        lean_dec_ref_known(v_a_3333_, 1);
                                        if lean_obj_tag(v_mvarIds_3360_) == 1 {
                                            v_tail_3361_ = lean_ctor_get(v_mvarIds_3360_, 1);
                                            if lean_obj_tag(v_tail_3361_) == 0 {
                                                lean_dec(v_a_3331_);
                                                v_head_3362_ = lean_ctor_get(v_mvarIds_3360_, 0);
                                                lean_inc(v_head_3362_);
                                                lean_dec_ref_known(v_mvarIds_3360_, 2);
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
                                                lean_dec_ref_known(v_mvarIds_3360_, 2);
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
                                            lean_dec(v_mvarIds_3360_);
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
                                        lean_dec(v_a_3333_);
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
                                    lean_dec(v_a_3331_);
                                    v_a_3363_ = lean_ctor_get(v___x_3332_, 0);
                                    v_isSharedCheck_3370_ = (!lean_is_exclusive(v___x_3332_)) as u8;
                                    if v_isSharedCheck_3370_ == 0 {
                                        v___x_3365_ = v___x_3332_;
                                        v_isShared_3366_ = v_isSharedCheck_3370_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3363_);
                                        lean_dec(v___x_3332_);
                                        v___x_3365_ = lean_box(0);
                                        v_isShared_3366_ = v_isSharedCheck_3370_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_3371_ = lean_ctor_get(v___x_3330_, 0);
                                v_isSharedCheck_3378_ = (!lean_is_exclusive(v___x_3330_)) as u8;
                                if v_isSharedCheck_3378_ == 0 {
                                    v___x_3373_ = v___x_3330_;
                                    v_isShared_3374_ = v_isSharedCheck_3378_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3371_);
                                    lean_dec(v___x_3330_);
                                    v___x_3373_ = lean_box(0);
                                    v_isShared_3374_ = v_isSharedCheck_3378_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_mvarIds_3326_, 2);
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_mvarIds_3326_);
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3318_);
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3321_ == 0 {
                    lean_ctor_set(v___x_3320_, 0, v___x_3316_);
                    v___x_3324_ = v___x_3320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3316_);
                    v___x_3324_ = v_reuseFailAlloc_3325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3324_;
            }
            5 => {
                lean_inc(v_goal_3335_);
                lean_inc_ref(v_applyPureConsEntailsRRule_3315_);
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
                if lean_obj_tag(v___x_3347_) == 0 {
                    v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
                    lean_inc(v_a_3348_);
                    lean_dec_ref_known(v___x_3347_, 1);
                    if lean_obj_tag(v_a_3348_) == 1 {
                        v_mvarIds_3349_ = lean_ctor_get(v_a_3348_, 0);
                        lean_inc(v_mvarIds_3349_);
                        lean_dec_ref_known(v_a_3348_, 1);
                        if lean_obj_tag(v_mvarIds_3349_) == 1 {
                            v_tail_3350_ = lean_ctor_get(v_mvarIds_3349_, 1);
                            if lean_obj_tag(v_tail_3350_) == 0 {
                                lean_dec(v_goal_3335_);
                                v_head_3351_ = lean_ctor_get(v_mvarIds_3349_, 0);
                                lean_inc(v_head_3351_);
                                lean_dec_ref_known(v_mvarIds_3349_, 2);
                                v_goal_3310_ = v_head_3351_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v_mvarIds_3349_, 2);
                                v_goal_3310_ = v_goal_3335_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarIds_3349_);
                            v_goal_3310_ = v_goal_3335_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3348_);
                        v_goal_3310_ = v_goal_3335_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_3335_);
                    v_a_3352_ = lean_ctor_get(v___x_3347_, 0);
                    v_isSharedCheck_3359_ = (!lean_is_exclusive(v___x_3347_)) as u8;
                    if v_isSharedCheck_3359_ == 0 {
                        v___x_3354_ = v___x_3347_;
                        v_isShared_3355_ = v_isSharedCheck_3359_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3352_);
                        lean_dec(v___x_3347_);
                        v___x_3354_ = lean_box(0);
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
                    v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
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
                    v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
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
                    v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
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
                    v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
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
    mut v_goal_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
    mut v_a_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3401_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3399_);
    lean_dec_ref(v_a_3398_);
    lean_dec(v_a_3397_);
    lean_dec_ref(v_a_3396_);
    lean_dec(v_a_3395_);
    lean_dec_ref(v_a_3394_);
    lean_dec(v_a_3393_);
    lean_dec_ref(v_a_3392_);
    lean_dec(v_a_3391_);
    lean_dec(v_a_3390_);
    lean_dec_ref(v_a_3389_);
    return v_res_3401_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    v___x_3403_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0;
    v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
    return v___x_3404_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v___x_3406_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2;
    v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
    return v___x_3407_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    v___x_3409_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4;
    v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
    return v___x_3410_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(
    mut v_a_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut v_a_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3424_ = lean_ctor_get(v_a_3411_, 0);
                v_snd_3425_ = lean_ctor_get(v_a_3411_, 1);
                v_isSharedCheck_3477_ = (!lean_is_exclusive(v_a_3411_)) as u8;
                if v_isSharedCheck_3477_ == 0 {
                    v___x_3427_ = v_a_3411_;
                    v_isShared_3428_ = v_isSharedCheck_3477_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3425_);
                    lean_inc(v_fst_3424_);
                    lean_dec(v_a_3411_);
                    v___x_3427_ = lean_box(0);
                    v_isShared_3428_ = v_isSharedCheck_3477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3429_ = lean_unsigned_to_nat(0);
                v___x_3430_ = lean_nat_dec_lt(v___x_3429_, v_fst_3424_);
                if v___x_3430_ == 0 {
                    if v_isShared_3428_ == 0 {
                        v___x_3432_ = v___x_3427_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_fst_3424_);
                        lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_snd_3425_);
                        v___x_3432_ = v_reuseFailAlloc_3434_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_snd_3425_);
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
                    if lean_obj_tag(v___x_3435_) == 0 {
                        v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
                        lean_inc(v_a_3436_);
                        lean_dec_ref_known(v___x_3435_, 1);
                        v___x_3437_ = lean_unsigned_to_nat(1);
                        v___x_3438_ = lean_nat_sub(v_fst_3424_, v___x_3437_);
                        lean_dec(v_fst_3424_);
                        if lean_obj_tag(v_a_3436_) == 1 {
                            lean_dec(v_snd_3425_);
                            v_val_3439_ = lean_ctor_get(v_a_3436_, 0);
                            lean_inc(v_val_3439_);
                            lean_dec_ref_known(v_a_3436_, 1);
                            if v_isShared_3428_ == 0 {
                                lean_ctor_set(v___x_3427_, 1, v_val_3439_);
                                lean_ctor_set(v___x_3427_, 0, v___x_3438_);
                                v___x_3441_ = v___x_3427_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3438_);
                                lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_val_3439_);
                                v___x_3441_ = v_reuseFailAlloc_3443_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3436_);
                            v___x_3444_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1);
                            lean_inc(v_snd_3425_);
                            v___x_3445_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3445_, 0, v_snd_3425_);
                            v___x_3446_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3446_, 0, v___x_3444_);
                            lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                            v___x_3447_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3);
                            v___x_3448_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3448_, 0, v___x_3446_);
                            lean_ctor_set(v___x_3448_, 1, v___x_3447_);
                            v___x_3449_ = lean_nat_add(v___x_3438_, v___x_3437_);
                            v___x_3450_ = l_Nat_reprFast(v___x_3449_);
                            v___x_3451_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                            v___x_3452_ = l_Lean_MessageData_ofFormat(v___x_3451_);
                            v___x_3453_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3453_, 0, v___x_3448_);
                            lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                            v___x_3454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5);
                            v___x_3455_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3455_, 0, v___x_3453_);
                            lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                            v___x_3456_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3455_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
                            if lean_obj_tag(v___x_3456_) == 0 {
                                lean_dec_ref_known(v___x_3456_, 1);
                                if v_isShared_3428_ == 0 {
                                    lean_ctor_set(v___x_3427_, 0, v___x_3438_);
                                    v___x_3458_ = v___x_3427_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3438_);
                                    lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_snd_3425_);
                                    v___x_3458_ = v_reuseFailAlloc_3460_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3438_);
                                lean_del_object(v___x_3427_);
                                lean_dec(v_snd_3425_);
                                v_a_3461_ = lean_ctor_get(v___x_3456_, 0);
                                v_isSharedCheck_3468_ = (!lean_is_exclusive(v___x_3456_)) as u8;
                                if v_isSharedCheck_3468_ == 0 {
                                    v___x_3463_ = v___x_3456_;
                                    v_isShared_3464_ = v_isSharedCheck_3468_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3461_);
                                    lean_dec(v___x_3456_);
                                    v___x_3463_ = lean_box(0);
                                    v_isShared_3464_ = v_isSharedCheck_3468_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3427_);
                        lean_dec(v_snd_3425_);
                        lean_dec(v_fst_3424_);
                        v_a_3469_ = lean_ctor_get(v___x_3435_, 0);
                        v_isSharedCheck_3476_ = (!lean_is_exclusive(v___x_3435_)) as u8;
                        if v_isSharedCheck_3476_ == 0 {
                            v___x_3471_ = v___x_3435_;
                            v_isShared_3472_ = v_isSharedCheck_3476_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3469_);
                            lean_dec(v___x_3435_);
                            v___x_3471_ = lean_box(0);
                            v_isShared_3472_ = v_isSharedCheck_3476_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3433_, 0, v___x_3432_);
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
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
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
                    v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
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
    mut v_a_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3491_: *mut LeanObject = core::ptr::null_mut();
    v_res_3491_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
    lean_dec(v___y_3489_);
    lean_dec_ref(v___y_3488_);
    lean_dec(v___y_3487_);
    lean_dec_ref(v___y_3486_);
    lean_dec(v___y_3485_);
    lean_dec_ref(v___y_3484_);
    lean_dec(v___y_3483_);
    lean_dec_ref(v___y_3482_);
    lean_dec(v___y_3481_);
    lean_dec(v___y_3480_);
    lean_dec_ref(v___y_3479_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(
    mut v_thm_3492_: *mut LeanObject,
    mut v_goal_3493_: *mut LeanObject,
    mut v_excessArgs_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v_snd_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_a_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_3507_ = lean_ctor_get(v_thm_3492_, 2);
                lean_inc_ref(v_kind_3507_);
                lean_dec_ref(v_thm_3492_);
                if lean_obj_tag(v_kind_3507_) == 0 {
                    v_etaPotential_3508_ = lean_ctor_get(v_kind_3507_, 0);
                    v_isSharedCheck_3542_ = (!lean_is_exclusive(v_kind_3507_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3510_ = v_kind_3507_;
                        v_isShared_3511_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_etaPotential_3508_);
                        lean_dec(v_kind_3507_);
                        v___x_3510_ = lean_box(0);
                        v_isShared_3511_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_kind_3507_);
                    lean_dec(v_goal_3493_);
                    v___x_3543_ = lean_box(0);
                    v___x_3544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                    return v___x_3544_;
                }
            }
            1 => {
                v___x_3512_ = lean_array_get_size(v_excessArgs_3494_);
                v_n_3513_ = lean_nat_sub(v_etaPotential_3508_, v___x_3512_);
                lean_dec(v_etaPotential_3508_);
                v___x_3514_ = lean_unsigned_to_nat(0);
                v___x_3515_ = lean_nat_dec_eq(v_n_3513_, v___x_3514_);
                if v___x_3515_ == 0 {
                    v___x_3516_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3516_, 0, v_n_3513_);
                    lean_ctor_set(v___x_3516_, 1, v_goal_3493_);
                    v___x_3517_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v___x_3516_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
                    if lean_obj_tag(v___x_3517_) == 0 {
                        v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
                        v_isSharedCheck_3529_ = (!lean_is_exclusive(v___x_3517_)) as u8;
                        if v_isSharedCheck_3529_ == 0 {
                            v___x_3520_ = v___x_3517_;
                            v_isShared_3521_ = v_isSharedCheck_3529_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3518_);
                            lean_dec(v___x_3517_);
                            v___x_3520_ = lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3529_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3510_);
                        v_a_3530_ = lean_ctor_get(v___x_3517_, 0);
                        v_isSharedCheck_3537_ = (!lean_is_exclusive(v___x_3517_)) as u8;
                        if v_isSharedCheck_3537_ == 0 {
                            v___x_3532_ = v___x_3517_;
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3530_);
                            lean_dec(v___x_3517_);
                            v___x_3532_ = lean_box(0);
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_n_3513_);
                    lean_dec(v_goal_3493_);
                    v___x_3538_ = lean_box(0);
                    if v_isShared_3511_ == 0 {
                        lean_ctor_set(v___x_3510_, 0, v___x_3538_);
                        v___x_3540_ = v___x_3510_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
                        v___x_3540_ = v_reuseFailAlloc_3541_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_3522_ = lean_ctor_get(v_a_3518_, 1);
                lean_inc(v_snd_3522_);
                lean_dec(v_a_3518_);
                if v_isShared_3511_ == 0 {
                    lean_ctor_set_tag(v___x_3510_, 1);
                    lean_ctor_set(v___x_3510_, 0, v_snd_3522_);
                    v___x_3524_ = v___x_3510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_snd_3522_);
                    v___x_3524_ = v_reuseFailAlloc_3528_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3521_ == 0 {
                    lean_ctor_set(v___x_3520_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
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
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
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
    mut v_thm_3545_: *mut LeanObject,
    mut v_goal_3546_: *mut LeanObject,
    mut v_excessArgs_3547_: *mut LeanObject,
    mut v_a_3548_: *mut LeanObject,
    mut v_a_3549_: *mut LeanObject,
    mut v_a_3550_: *mut LeanObject,
    mut v_a_3551_: *mut LeanObject,
    mut v_a_3552_: *mut LeanObject,
    mut v_a_3553_: *mut LeanObject,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
    mut v_a_3556_: *mut LeanObject,
    mut v_a_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
    mut v_a_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3560_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3558_);
    lean_dec_ref(v_a_3557_);
    lean_dec(v_a_3556_);
    lean_dec_ref(v_a_3555_);
    lean_dec(v_a_3554_);
    lean_dec_ref(v_a_3553_);
    lean_dec(v_a_3552_);
    lean_dec_ref(v_a_3551_);
    lean_dec(v_a_3550_);
    lean_dec(v_a_3549_);
    lean_dec_ref(v_a_3548_);
    lean_dec_ref(v_excessArgs_3547_);
    return v_res_3560_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(
    mut v_inst_3561_: *mut LeanObject,
    mut v_a_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    v___x_3575_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    return v___x_3575_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___boxed(
    mut v_inst_3576_: *mut LeanObject,
    mut v_a_3577_: *mut LeanObject,
    mut v___y_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
    mut v___y_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3590_: *mut LeanObject = core::ptr::null_mut();
    v_res_3590_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(v_inst_3576_, v_a_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
    lean_dec(v___y_3588_);
    lean_dec_ref(v___y_3587_);
    lean_dec(v___y_3586_);
    lean_dec_ref(v___y_3585_);
    lean_dec(v___y_3584_);
    lean_dec_ref(v___y_3583_);
    lean_dec(v___y_3582_);
    lean_dec_ref(v___y_3581_);
    lean_dec(v___y_3580_);
    lean_dec(v___y_3579_);
    lean_dec_ref(v___y_3578_);
    return v_res_3590_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(
    mut v_progress_3591_: u8,
    mut v_a_3592_: *mut LeanObject,
    mut v___y_3593_: *mut LeanObject,
    mut v___y_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
    mut v___y_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3609_: u8 = 0;
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_val_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut v_a_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3605_ = lean_ctor_get(v_a_3592_, 0);
                v_snd_3606_ = lean_ctor_get(v_a_3592_, 1);
                v_isSharedCheck_3636_ = (!lean_is_exclusive(v_a_3592_)) as u8;
                if v_isSharedCheck_3636_ == 0 {
                    v___x_3608_ = v_a_3592_;
                    v_isShared_3609_ = v_isSharedCheck_3636_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3606_);
                    lean_inc(v_fst_3605_);
                    lean_dec(v_a_3592_);
                    v___x_3608_ = lean_box(0);
                    v_isShared_3609_ = v_isSharedCheck_3636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_3606_);
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
                if lean_obj_tag(v___x_3610_) == 0 {
                    v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3627_ = (!lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3627_ == 0 {
                        v___x_3613_ = v___x_3610_;
                        v_isShared_3614_ = v_isSharedCheck_3627_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3611_);
                        lean_dec(v___x_3610_);
                        v___x_3613_ = lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3627_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3608_);
                    lean_dec(v_snd_3606_);
                    lean_dec(v_fst_3605_);
                    v_a_3628_ = lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3635_ = (!lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3635_ == 0 {
                        v___x_3630_ = v___x_3610_;
                        v_isShared_3631_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3628_);
                        lean_dec(v___x_3610_);
                        v___x_3630_ = lean_box(0);
                        v_isShared_3631_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3611_) == 1 {
                    lean_del_object(v___x_3613_);
                    lean_dec(v_snd_3606_);
                    lean_dec(v_fst_3605_);
                    v_val_3615_ = lean_ctor_get(v_a_3611_, 0);
                    lean_inc(v_val_3615_);
                    lean_dec_ref_known(v_a_3611_, 1);
                    v___x_3616_ = lean_box((v_progress_3591_) as usize);
                    if v_isShared_3609_ == 0 {
                        lean_ctor_set(v___x_3608_, 1, v_val_3615_);
                        lean_ctor_set(v___x_3608_, 0, v___x_3616_);
                        v___x_3618_ = v___x_3608_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3616_);
                        lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_val_3615_);
                        v___x_3618_ = v_reuseFailAlloc_3620_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3611_);
                    if v_isShared_3609_ == 0 {
                        v___x_3622_ = v___x_3608_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_fst_3605_);
                        lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_snd_3606_);
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
                    lean_ctor_set(v___x_3613_, 0, v___x_3622_);
                    v___x_3624_ = v___x_3613_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
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
                    v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
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
    mut v_progress_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_progress_boxed_3651_: u8 = 0;
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_progress_boxed_3651_ = (lean_unbox(v_progress_3637_) as u8);
    v_res_3652_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_boxed_3651_, v_a_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
    lean_dec(v___y_3649_);
    lean_dec_ref(v___y_3648_);
    lean_dec(v___y_3647_);
    lean_dec_ref(v___y_3646_);
    lean_dec(v___y_3645_);
    lean_dec_ref(v___y_3644_);
    lean_dec(v___y_3643_);
    lean_dec_ref(v___y_3642_);
    lean_dec(v___y_3641_);
    lean_dec(v___y_3640_);
    lean_dec_ref(v___y_3639_);
    return v_res_3652_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2()
-> *mut LeanObject {
    let mut v_progress_3659_: u8 = 0;
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v_progress_3659_ = 0;
    v___x_3660_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1;
    v___x_3661_ = l_Lean_MessageData_ofConstName(v___x_3660_, v_progress_3659_);
    return v___x_3661_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    v___x_3662_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2,
    );
    v___x_3663_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3664_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    lean_ctor_set(v___x_3664_, 1, v___x_3662_);
    return v___x_3664_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8()
-> *mut LeanObject {
    let mut v_progress_3677_: u8 = 0;
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v_progress_3677_ = 0;
    v___x_3678_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7;
    v___x_3679_ = l_Lean_MessageData_ofConstName(v___x_3678_, v_progress_3677_);
    return v___x_3679_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    v___x_3680_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8,
    );
    v___x_3681_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3682_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3682_, 0, v___x_3681_);
    lean_ctor_set(v___x_3682_, 1, v___x_3680_);
    return v___x_3682_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12()
-> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    v___x_3685_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11;
    v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15()
-> *mut LeanObject {
    let mut v_progress_3693_: u8 = 0;
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v_progress_3693_ = 0;
    v___x_3694_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14;
    v___x_3695_ = l_Lean_MessageData_ofConstName(v___x_3694_, v_progress_3693_);
    return v___x_3695_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16()
-> *mut LeanObject {
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3696_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15,
    );
    v___x_3697_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12,
    );
    v___x_3698_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3698_, 0, v___x_3697_);
    lean_ctor_set(v___x_3698_, 1, v___x_3696_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3699_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3700_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16,
    );
    v___x_3701_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    lean_ctor_set(v___x_3701_, 1, v___x_3699_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18()
-> *mut LeanObject {
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    v___x_3702_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2,
    );
    v___x_3703_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12,
    );
    v___x_3704_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3704_, 0, v___x_3703_);
    lean_ctor_set(v___x_3704_, 1, v___x_3702_);
    return v___x_3704_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3706_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18,
    );
    v___x_3707_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3707_, 0, v___x_3706_);
    lean_ctor_set(v___x_3707_, 1, v___x_3705_);
    return v___x_3707_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21()
-> *mut LeanObject {
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v___x_3710_ = lean_box(0);
    v___x_3711_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20;
    v___x_3712_ = l_Lean_mkConst(v___x_3711_, v___x_3710_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(
    mut v_goal_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
    mut v___y_3718_: *mut LeanObject,
    mut v___y_3719_: *mut LeanObject,
    mut v___y_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_progress_3729_: u8 = 0;
    let mut v_goal_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: u8 = 0;
    let mut v_progress_3737_: u8 = 0;
    let mut v_goal_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3764_: u8 = 0;
    let mut v___y_3766_: u8 = 0;
    let mut v_progress_3767_: u8 = 0;
    let mut v_goal_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v___y_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v_arg_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: u8 = 0;
    let mut v_arg_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_progress_3836_: u8 = 0;
    let mut v_progress_3837_: u8 = 0;
    let mut v___y_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: u8 = 0;
    let mut v_downPureIntroRule_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureElimRule_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3868_: u8 = 0;
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: u8 = 0;
    let mut v_a_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_progress_3887_: u8 = 0;
    let mut v___y_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    let mut v_arg_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v_entailsNilIntroRule_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v___x_3937_: u8 = 0;
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut v_a_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v_downPureIntroRule_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v_a_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3960_: u8 = 0;
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3964_: u8 = 0;
    let mut v_a_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v___y_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: u8 = 0;
    let mut v___y_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_a_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4008_: u8 = 0;
    let mut v___y_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_progress_4011_: u8 = 0;
    let mut v_goal_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v_pureIntroRule_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_mvarIds_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_a_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_progress_4057_: u8 = 0;
    let mut v_goal_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_a_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureHNonTrue_4109_: u8 = 0;
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pureElimRule_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v_a_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v___y_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut v_a_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v_a_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v___y_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4178_: u8 = 0;
    let mut v_a_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_3715_);
                v___x_3816_ = l_Lean_MVarId_getType(
                    v_goal_3715_,
                    v___y_3723_,
                    v___y_3724_,
                    v___y_3725_,
                    v___y_3726_,
                );
                if lean_obj_tag(v___x_3816_) == 0 {
                    v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
                    v_isSharedCheck_4178_ = (!lean_is_exclusive(v___x_3816_)) as u8;
                    if v_isSharedCheck_4178_ == 0 {
                        v___x_3819_ = v___x_3816_;
                        v_isShared_3820_ = v_isSharedCheck_4178_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3817_);
                        lean_dec(v___x_3816_);
                        v___x_3819_ = lean_box(0);
                        v_isShared_3820_ = v_isSharedCheck_4178_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_3715_);
                    v_a_4179_ = lean_ctor_get(v___x_3816_, 0);
                    v_isSharedCheck_4186_ = (!lean_is_exclusive(v___x_3816_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4181_ = v___x_3816_;
                        v_isShared_4182_ = v_isSharedCheck_4186_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_a_4179_);
                        lean_dec(v___x_3816_);
                        v___x_4181_ = lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4186_;
                        state = 55;
                        continue;
                    }
                }
            }
            1 => {
                if v_progress_3729_ == 0 {
                    lean_dec(v_goal_3730_);
                    v___x_3731_ = lean_box(0);
                    v___x_3732_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3732_, 0, v___x_3731_);
                    return v___x_3732_;
                } else {
                    v___x_3733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3733_, 0, v_goal_3730_);
                    v___x_3734_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3734_, 0, v___x_3733_);
                    return v___x_3734_;
                }
            }
            2 => {
                v___x_3751_ = lean_box(0);
                lean_inc(v_goal_3738_);
                lean_inc_ref(v_downPureIntroRule_3740_);
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
                if lean_obj_tag(v___x_3752_) == 0 {
                    v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
                    lean_inc(v_a_3753_);
                    lean_dec_ref_known(v___x_3752_, 1);
                    if lean_obj_tag(v_a_3753_) == 1 {
                        v_mvarIds_3754_ = lean_ctor_get(v_a_3753_, 0);
                        lean_inc(v_mvarIds_3754_);
                        lean_dec_ref_known(v_a_3753_, 1);
                        if lean_obj_tag(v_mvarIds_3754_) == 1 {
                            v_tail_3755_ = lean_ctor_get(v_mvarIds_3754_, 1);
                            if lean_obj_tag(v_tail_3755_) == 0 {
                                lean_dec(v_goal_3738_);
                                v_head_3756_ = lean_ctor_get(v_mvarIds_3754_, 0);
                                lean_inc(v_head_3756_);
                                lean_dec_ref_known(v_mvarIds_3754_, 2);
                                v_progress_3729_ = v___y_3736_;
                                v_goal_3730_ = v_head_3756_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v_mvarIds_3754_, 2);
                                v_progress_3729_ = v_progress_3737_;
                                v_goal_3730_ = v_goal_3738_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarIds_3754_);
                            v_progress_3729_ = v_progress_3737_;
                            v_goal_3730_ = v_goal_3738_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3753_);
                        v_progress_3729_ = v_progress_3737_;
                        v_goal_3730_ = v_goal_3738_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_3738_);
                    v_a_3757_ = lean_ctor_get(v___x_3752_, 0);
                    v_isSharedCheck_3764_ = (!lean_is_exclusive(v___x_3752_)) as u8;
                    if v_isSharedCheck_3764_ == 0 {
                        v___x_3759_ = v___x_3752_;
                        v_isShared_3760_ = v_isSharedCheck_3764_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3757_);
                        lean_dec(v___x_3752_);
                        v___x_3759_ = lean_box(0);
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
                    v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
                    v___x_3762_ = v_reuseFailAlloc_3763_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3762_;
            }
            5 => {
                v___x_3782_ = lean_box(0);
                lean_inc(v_goal_3768_);
                lean_inc_ref(v_pureIntroRule_3771_);
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
                if lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
                    lean_inc(v_a_3784_);
                    lean_dec_ref_known(v___x_3783_, 1);
                    if lean_obj_tag(v_a_3784_) == 1 {
                        v_mvarIds_3785_ = lean_ctor_get(v_a_3784_, 0);
                        lean_inc(v_mvarIds_3785_);
                        lean_dec_ref_known(v_a_3784_, 1);
                        if lean_obj_tag(v_mvarIds_3785_) == 1 {
                            v_tail_3786_ = lean_ctor_get(v_mvarIds_3785_, 1);
                            if lean_obj_tag(v_tail_3786_) == 0 {
                                lean_dec(v_goal_3768_);
                                v_head_3787_ = lean_ctor_get(v_mvarIds_3785_, 0);
                                lean_inc(v_head_3787_);
                                lean_dec_ref_known(v_mvarIds_3785_, 2);
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
                                lean_dec_ref_known(v_mvarIds_3785_, 2);
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
                            lean_dec(v_mvarIds_3785_);
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
                        lean_dec(v_a_3784_);
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
                    lean_dec(v_goal_3768_);
                    v_a_3788_ = lean_ctor_get(v___x_3783_, 0);
                    v_isSharedCheck_3795_ = (!lean_is_exclusive(v___x_3783_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3783_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3788_);
                        lean_dec(v___x_3783_);
                        v___x_3790_ = lean_box(0);
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
                    v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
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
                if lean_obj_tag(v___x_3802_) == 0 {
                    v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
                    lean_inc(v_a_3803_);
                    lean_dec_ref_known(v___x_3802_, 1);
                    v___x_3804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
                    v___x_3805_ = l_Lean_MessageData_ofExpr(v_a_3803_);
                    v___x_3806_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3806_, 0, v___x_3804_);
                    lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                    v___x_3807_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3806_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
                    return v___x_3807_;
                } else {
                    v_a_3808_ = lean_ctor_get(v___x_3802_, 0);
                    v_isSharedCheck_3815_ = (!lean_is_exclusive(v___x_3802_)) as u8;
                    if v_isSharedCheck_3815_ == 0 {
                        v___x_3810_ = v___x_3802_;
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3808_);
                        lean_dec(v___x_3802_);
                        v___x_3810_ = lean_box(0);
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
                    v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
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
                    lean_dec_ref(v___x_3826_);
                    lean_dec(v_goal_3715_);
                    state = 12;
                    continue;
                } else {
                    v_arg_3828_ = lean_ctor_get(v___x_3826_, 1);
                    lean_inc_ref(v_arg_3828_);
                    v___x_3829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3826_);
                    v___x_3830_ = l_Lean_Expr_isApp(v___x_3829_);
                    if v___x_3830_ == 0 {
                        lean_dec_ref(v___x_3829_);
                        lean_dec_ref(v_arg_3828_);
                        lean_dec(v_goal_3715_);
                        state = 12;
                        continue;
                    } else {
                        v_arg_3831_ = lean_ctor_get(v___x_3829_, 1);
                        lean_inc_ref(v_arg_3831_);
                        v___x_3832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3829_);
                        v___x_3833_ = l_Lean_Expr_isApp(v___x_3832_);
                        if v___x_3833_ == 0 {
                            lean_dec_ref(v___x_3832_);
                            lean_dec_ref(v_arg_3831_);
                            lean_dec_ref(v_arg_3828_);
                            lean_dec(v_goal_3715_);
                            state = 12;
                            continue;
                        } else {
                            v___x_3834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3832_);
                            v___x_3835_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6;
                            v_progress_3836_ = l_Lean_Expr_isConstOf(v___x_3834_, v___x_3835_);
                            lean_dec_ref(v___x_3834_);
                            if v_progress_3836_ == 0 {
                                lean_dec_ref(v_arg_3831_);
                                lean_dec_ref(v_arg_3828_);
                                lean_dec(v_goal_3715_);
                                state = 12;
                                continue;
                            } else {
                                lean_del_object(v___x_3819_);
                                v_progress_3837_ = 0;
                                v___x_3884_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5;
                                v___x_4173_ = lean_unsigned_to_nat(2);
                                v___x_4174_ =
                                    l_Lean_Expr_isAppOfArity(v_arg_3831_, v___x_3884_, v___x_4173_);
                                if v___x_4174_ == 0 {
                                    lean_dec_ref(v_arg_3831_);
                                    v___x_4175_ = lean_box(0);
                                    v___y_4167_ = v___x_4175_;
                                    state = 54;
                                    continue;
                                } else {
                                    v___x_4176_ = l_Lean_Expr_appArg_x21(v_arg_3831_);
                                    lean_dec_ref(v_arg_3831_);
                                    v___x_4177_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_4177_, 0, v___x_4176_);
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
                v___x_3822_ = lean_box(0);
                if v_isShared_3820_ == 0 {
                    lean_ctor_set(v___x_3819_, 0, v___x_3822_);
                    v___x_3824_ = v___x_3819_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
                    v___x_3824_ = v_reuseFailAlloc_3825_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3824_;
            }
            14 => {
                v_downPureIntroRule_3853_ = lean_ctor_get(v___y_3850_, 5);
                v_pureElimRule_3854_ = lean_ctor_get(v___y_3850_, 6);
                v_pureIntroRule_3855_ = lean_ctor_get(v___y_3850_, 7);
                v___x_3856_ = lean_box(0);
                lean_inc(v___y_3840_);
                lean_inc_ref(v_pureElimRule_3854_);
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
                if lean_obj_tag(v___x_3857_) == 0 {
                    v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
                    lean_inc(v_a_3858_);
                    lean_dec_ref_known(v___x_3857_, 1);
                    if lean_obj_tag(v_a_3858_) == 1 {
                        v_mvarIds_3859_ = lean_ctor_get(v_a_3858_, 0);
                        lean_inc(v_mvarIds_3859_);
                        lean_dec_ref_known(v_a_3858_, 1);
                        if lean_obj_tag(v_mvarIds_3859_) == 1 {
                            v_tail_3860_ = lean_ctor_get(v_mvarIds_3859_, 1);
                            if lean_obj_tag(v_tail_3860_) == 0 {
                                lean_dec(v___y_3845_);
                                lean_dec(v___y_3840_);
                                v_head_3861_ = lean_ctor_get(v_mvarIds_3859_, 0);
                                lean_inc(v_head_3861_);
                                lean_dec_ref_known(v_mvarIds_3859_, 2);
                                v___x_3862_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
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
                                if lean_obj_tag(v___x_3863_) == 0 {
                                    v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
                                    lean_inc(v_a_3864_);
                                    lean_dec_ref_known(v___x_3863_, 1);
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
                                    v_a_3865_ = lean_ctor_get(v___x_3863_, 0);
                                    v_isSharedCheck_3872_ = (!lean_is_exclusive(v___x_3863_)) as u8;
                                    if v_isSharedCheck_3872_ == 0 {
                                        v___x_3867_ = v___x_3863_;
                                        v_isShared_3868_ = v_isSharedCheck_3872_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3865_);
                                        lean_dec(v___x_3863_);
                                        v___x_3867_ = lean_box(0);
                                        v_isShared_3868_ = v_isSharedCheck_3872_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_mvarIds_3859_, 2);
                                v___x_3873_ = (lean_unbox(v___y_3845_) as u8);
                                lean_dec(v___y_3845_);
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
                            lean_dec(v_mvarIds_3859_);
                            v___x_3874_ = (lean_unbox(v___y_3845_) as u8);
                            lean_dec(v___y_3845_);
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
                        lean_dec(v_a_3858_);
                        v___x_3875_ = (lean_unbox(v___y_3845_) as u8);
                        lean_dec(v___y_3845_);
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
                    lean_dec(v___y_3845_);
                    lean_dec(v___y_3840_);
                    v_a_3876_ = lean_ctor_get(v___x_3857_, 0);
                    v_isSharedCheck_3883_ = (!lean_is_exclusive(v___x_3857_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3878_ = v___x_3857_;
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3876_);
                        lean_dec(v___x_3857_);
                        v___x_3878_ = lean_box(0);
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
                    v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
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
                    v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3881_;
            }
            19 => {
                v___x_3899_ = lean_box((v_progress_3887_) as usize);
                v___x_3900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                lean_ctor_set(v___x_3900_, 1, v___y_3886_);
                v___x_3901_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_3836_, v___x_3900_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                if lean_obj_tag(v___x_3901_) == 0 {
                    v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
                    lean_inc(v_a_3902_);
                    lean_dec_ref_known(v___x_3901_, 1);
                    v_fst_3903_ = lean_ctor_get(v_a_3902_, 0);
                    lean_inc(v_fst_3903_);
                    v_snd_3904_ = lean_ctor_get(v_a_3902_, 1);
                    lean_inc_n(v_snd_3904_, 2);
                    lean_dec(v_a_3902_);
                    v___x_3905_ = l_Lean_MVarId_getType(
                        v_snd_3904_,
                        v___y_3895_,
                        v___y_3896_,
                        v___y_3897_,
                        v___y_3898_,
                    );
                    if lean_obj_tag(v___x_3905_) == 0 {
                        v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
                        lean_inc(v_a_3906_);
                        lean_dec_ref_known(v___x_3905_, 1);
                        v___x_3907_ = l_Lean_Expr_cleanupAnnotations(v_a_3906_);
                        v___x_3908_ = l_Lean_Expr_isApp(v___x_3907_);
                        if v___x_3908_ == 0 {
                            lean_dec_ref(v___x_3907_);
                            lean_dec(v_fst_3903_);
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
                                lean_dec_ref(v___x_3909_);
                                lean_dec(v_fst_3903_);
                                v___y_3797_ = v_snd_3904_;
                                v___y_3798_ = v___y_3895_;
                                v___y_3799_ = v___y_3896_;
                                v___y_3800_ = v___y_3897_;
                                v___y_3801_ = v___y_3898_;
                                state = 8;
                                continue;
                            } else {
                                v_arg_3911_ = lean_ctor_get(v___x_3909_, 1);
                                lean_inc_ref(v_arg_3911_);
                                v___x_3912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3909_);
                                v___x_3913_ = l_Lean_Expr_isApp(v___x_3912_);
                                if v___x_3913_ == 0 {
                                    lean_dec_ref(v___x_3912_);
                                    lean_dec_ref(v_arg_3911_);
                                    lean_dec(v_fst_3903_);
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
                                    lean_dec_ref(v___x_3914_);
                                    if v___x_3915_ == 0 {
                                        lean_dec_ref(v_arg_3911_);
                                        lean_dec(v_fst_3903_);
                                        v___y_3797_ = v_snd_3904_;
                                        v___y_3798_ = v___y_3895_;
                                        v___y_3799_ = v___y_3896_;
                                        v___y_3800_ = v___y_3897_;
                                        v___y_3801_ = v___y_3898_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_3916_ = lean_unsigned_to_nat(2);
                                        v___x_3917_ = l_Lean_Expr_isAppOfArity(
                                            v_arg_3911_,
                                            v___x_3884_,
                                            v___x_3916_,
                                        );
                                        if v___x_3917_ == 0 {
                                            lean_dec_ref(v_arg_3911_);
                                            v_entailsNilIntroRule_3918_ =
                                                lean_ctor_get(v___y_3888_, 2);
                                            v_downPureIntroRule_3919_ =
                                                lean_ctor_get(v___y_3888_, 5);
                                            v___x_3920_ = lean_box(0);
                                            lean_inc(v_snd_3904_);
                                            lean_inc_ref(v_entailsNilIntroRule_3918_);
                                            v___x_3921_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsNilIntroRule_3918_, v_snd_3904_, v___x_3920_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                                            if lean_obj_tag(v___x_3921_) == 0 {
                                                v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
                                                lean_inc(v_a_3922_);
                                                lean_dec_ref_known(v___x_3921_, 1);
                                                if lean_obj_tag(v_a_3922_) == 1 {
                                                    v_mvarIds_3923_ = lean_ctor_get(v_a_3922_, 0);
                                                    lean_inc(v_mvarIds_3923_);
                                                    lean_dec_ref_known(v_a_3922_, 1);
                                                    if lean_obj_tag(v_mvarIds_3923_) == 1 {
                                                        v_tail_3924_ =
                                                            lean_ctor_get(v_mvarIds_3923_, 1);
                                                        if lean_obj_tag(v_tail_3924_) == 0 {
                                                            lean_dec(v_snd_3904_);
                                                            lean_dec(v_fst_3903_);
                                                            v_head_3925_ =
                                                                lean_ctor_get(v_mvarIds_3923_, 0);
                                                            lean_inc(v_head_3925_);
                                                            lean_dec_ref_known(v_mvarIds_3923_, 2);
                                                            v___x_3926_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9);
                                                            v___x_3927_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_3925_, v___x_3926_, v___y_3888_, v___y_3889_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                                                            if lean_obj_tag(v___x_3927_) == 0 {
                                                                v_a_3928_ =
                                                                    lean_ctor_get(v___x_3927_, 0);
                                                                lean_inc(v_a_3928_);
                                                                lean_dec_ref_known(v___x_3927_, 1);
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
                                                                    lean_ctor_get(v___x_3927_, 0);
                                                                v_isSharedCheck_3936_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3927_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3936_ == 0 {
                                                                    v___x_3931_ = v___x_3927_;
                                                                    v_isShared_3932_ =
                                                                        v_isSharedCheck_3936_;
                                                                    state = 20;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3929_);
                                                                    lean_dec(v___x_3927_);
                                                                    v___x_3931_ = lean_box(0);
                                                                    v_isShared_3932_ =
                                                                        v_isSharedCheck_3936_;
                                                                    state = 20;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref_known(v_mvarIds_3923_, 2);
                                                            v___x_3937_ =
                                                                (lean_unbox(v_fst_3903_) as u8);
                                                            lean_dec(v_fst_3903_);
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
                                                        lean_dec(v_mvarIds_3923_);
                                                        v___x_3938_ =
                                                            (lean_unbox(v_fst_3903_) as u8);
                                                        lean_dec(v_fst_3903_);
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
                                                    lean_dec(v_a_3922_);
                                                    v___x_3939_ = (lean_unbox(v_fst_3903_) as u8);
                                                    lean_dec(v_fst_3903_);
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
                                                lean_dec(v_snd_3904_);
                                                lean_dec(v_fst_3903_);
                                                v_a_3940_ = lean_ctor_get(v___x_3921_, 0);
                                                v_isSharedCheck_3947_ =
                                                    (!lean_is_exclusive(v___x_3921_)) as u8;
                                                if v_isSharedCheck_3947_ == 0 {
                                                    v___x_3942_ = v___x_3921_;
                                                    v_isShared_3943_ = v_isSharedCheck_3947_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3940_);
                                                    lean_dec(v___x_3921_);
                                                    v___x_3942_ = lean_box(0);
                                                    v_isShared_3943_ = v_isSharedCheck_3947_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_3948_ = l_Lean_Expr_appArg_x21(v_arg_3911_);
                                            lean_dec_ref(v_arg_3911_);
                                            if lean_obj_tag(v___x_3948_) == 4 {
                                                v_declName_3949_ = lean_ctor_get(v___x_3948_, 0);
                                                lean_inc(v_declName_3949_);
                                                lean_dec_ref_known(v___x_3948_, 2);
                                                if lean_obj_tag(v_declName_3949_) == 1 {
                                                    v_pre_3950_ =
                                                        lean_ctor_get(v_declName_3949_, 0);
                                                    if lean_obj_tag(v_pre_3950_) == 0 {
                                                        v_str_3951_ =
                                                            lean_ctor_get(v_declName_3949_, 1);
                                                        lean_inc_ref(v_str_3951_);
                                                        lean_dec_ref_known(v_declName_3949_, 2);
                                                        v___x_3952_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10;
                                                        v___x_3953_ = lean_string_dec_eq(
                                                            v_str_3951_,
                                                            v___x_3952_,
                                                        );
                                                        lean_dec_ref(v_str_3951_);
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
                                                                    lean_ctor_get(v___y_3888_, 5);
                                                                v_pureIntroRule_3955_ =
                                                                    lean_ctor_get(v___y_3888_, 7);
                                                                v___x_3956_ =
                                                                    (lean_unbox(v_fst_3903_) as u8);
                                                                lean_dec(v_fst_3903_);
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
                                                        lean_dec_ref_known(v_declName_3949_, 2);
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
                                                    lean_dec(v_declName_3949_);
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
                                                lean_dec_ref(v___x_3948_);
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
                        lean_dec(v_snd_3904_);
                        lean_dec(v_fst_3903_);
                        v_a_3957_ = lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3964_ = (!lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3964_ == 0 {
                            v___x_3959_ = v___x_3905_;
                            v_isShared_3960_ = v_isSharedCheck_3964_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_3957_);
                            lean_dec(v___x_3905_);
                            v___x_3959_ = lean_box(0);
                            v_isShared_3960_ = v_isSharedCheck_3964_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    v_a_3965_ = lean_ctor_get(v___x_3901_, 0);
                    v_isSharedCheck_3972_ = (!lean_is_exclusive(v___x_3901_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3967_ = v___x_3901_;
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_3965_);
                        lean_dec(v___x_3901_);
                        v___x_3967_ = lean_box(0);
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
                    v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
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
                    v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
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
                    v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
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
                    v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
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
                if lean_obj_tag(v___x_3987_) == 0 {
                    v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
                    lean_inc(v_a_3988_);
                    lean_dec_ref_known(v___x_3987_, 1);
                    v___x_3989_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17);
                    v___x_3990_ = l_Lean_MessageData_ofExpr(v_a_3988_);
                    v___x_3991_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3991_, 0, v___x_3989_);
                    lean_ctor_set(v___x_3991_, 1, v___x_3990_);
                    v___x_3992_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3991_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
                    v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
                    v_isSharedCheck_4000_ = (!lean_is_exclusive(v___x_3992_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3995_ = v___x_3992_;
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3993_);
                        lean_dec(v___x_3992_);
                        v___x_3995_ = lean_box(0);
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 29;
                        continue;
                    }
                } else {
                    v_a_4001_ = lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_4008_ = (!lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4008_ == 0 {
                        v___x_4003_ = v___x_3987_;
                        v_isShared_4004_ = v_isSharedCheck_4008_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_4001_);
                        lean_dec(v___x_3987_);
                        v___x_4003_ = lean_box(0);
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
                    v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
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
                    v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
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
                    lean_dec(v___y_4010_);
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
                    if lean_obj_tag(v___y_4010_) == 0 {
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
                        v_isSharedCheck_4052_ = (!lean_is_exclusive(v___y_4010_)) as u8;
                        if v_isSharedCheck_4052_ == 0 {
                            v_unused_4053_ = lean_ctor_get(v___y_4010_, 0);
                            lean_dec(v_unused_4053_);
                            v___x_4025_ = v___y_4010_;
                            v_isShared_4026_ = v_isSharedCheck_4052_;
                            state = 34;
                            continue;
                        } else {
                            lean_dec(v___y_4010_);
                            v___x_4025_ = lean_box(0);
                            v_isShared_4026_ = v_isSharedCheck_4052_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            34 => {
                v_pureIntroRule_4027_ = lean_ctor_get(v___y_4013_, 7);
                v___x_4028_ = lean_box(0);
                lean_inc(v_goal_4012_);
                lean_inc_ref(v_pureIntroRule_4027_);
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
                if lean_obj_tag(v___x_4029_) == 0 {
                    v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4043_ = (!lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4043_ == 0 {
                        v___x_4032_ = v___x_4029_;
                        v_isShared_4033_ = v_isSharedCheck_4043_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_4030_);
                        lean_dec(v___x_4029_);
                        v___x_4032_ = lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4043_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4025_);
                    lean_dec(v_goal_4012_);
                    v_a_4044_ = lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4051_ = (!lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4051_ == 0 {
                        v___x_4046_ = v___x_4029_;
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_4044_);
                        lean_dec(v___x_4029_);
                        v___x_4046_ = lean_box(0);
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if lean_obj_tag(v_a_4030_) == 1 {
                    v_mvarIds_4034_ = lean_ctor_get(v_a_4030_, 0);
                    lean_inc(v_mvarIds_4034_);
                    lean_dec_ref_known(v_a_4030_, 1);
                    if lean_obj_tag(v_mvarIds_4034_) == 1 {
                        v_tail_4035_ = lean_ctor_get(v_mvarIds_4034_, 1);
                        if lean_obj_tag(v_tail_4035_) == 0 {
                            lean_dec(v_goal_4012_);
                            v_head_4036_ = lean_ctor_get(v_mvarIds_4034_, 0);
                            lean_inc(v_head_4036_);
                            lean_dec_ref_known(v_mvarIds_4034_, 2);
                            if v_isShared_4026_ == 0 {
                                lean_ctor_set(v___x_4025_, 0, v_head_4036_);
                                v___x_4038_ = v___x_4025_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_head_4036_);
                                v___x_4038_ = v_reuseFailAlloc_4042_;
                                state = 36;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_mvarIds_4034_, 2);
                            lean_del_object(v___x_4032_);
                            lean_del_object(v___x_4025_);
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
                        lean_dec(v_mvarIds_4034_);
                        lean_del_object(v___x_4032_);
                        lean_del_object(v___x_4025_);
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
                    lean_del_object(v___x_4032_);
                    lean_dec(v_a_4030_);
                    lean_del_object(v___x_4025_);
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
                    lean_ctor_set(v___x_4032_, 0, v___x_4038_);
                    v___x_4040_ = v___x_4032_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
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
                    v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
                    v___x_4049_ = v_reuseFailAlloc_4050_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4049_;
            }
            40 => {
                if lean_obj_tag(v___y_4055_) == 0 {
                    lean_dec(v___y_4056_);
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
                    lean_dec_ref_known(v___y_4055_, 1);
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
                lean_dec(v___y_4072_);
                lean_dec(v___y_4071_);
                v___x_4084_ = l_Lean_MVarId_getType(
                    v_goal_3715_,
                    v___y_4080_,
                    v___y_4081_,
                    v___y_4082_,
                    v___y_4083_,
                );
                if lean_obj_tag(v___x_4084_) == 0 {
                    v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
                    lean_inc(v_a_4085_);
                    lean_dec_ref_known(v___x_4084_, 1);
                    v___x_4086_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19);
                    v___x_4087_ = l_Lean_MessageData_ofExpr(v_a_4085_);
                    v___x_4088_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4088_, 0, v___x_4086_);
                    lean_ctor_set(v___x_4088_, 1, v___x_4087_);
                    v___x_4089_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_4088_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
                    v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
                    v_isSharedCheck_4097_ = (!lean_is_exclusive(v___x_4089_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4092_ = v___x_4089_;
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_4090_);
                        lean_dec(v___x_4089_);
                        v___x_4092_ = lean_box(0);
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 42;
                        continue;
                    }
                } else {
                    v_a_4098_ = lean_ctor_get(v___x_4084_, 0);
                    v_isSharedCheck_4105_ = (!lean_is_exclusive(v___x_4084_)) as u8;
                    if v_isSharedCheck_4105_ == 0 {
                        v___x_4100_ = v___x_4084_;
                        v_isShared_4101_ = v_isSharedCheck_4105_;
                        state = 44;
                        continue;
                    } else {
                        lean_inc(v_a_4098_);
                        lean_dec(v___x_4084_);
                        v___x_4100_ = lean_box(0);
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
                    v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
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
                    v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
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
                    v_pureElimRule_4121_ = lean_ctor_get(v___y_4110_, 6);
                    v___x_4122_ = lean_box(0);
                    lean_inc(v_goal_3715_);
                    lean_inc_ref(v_pureElimRule_4121_);
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
                    if lean_obj_tag(v___x_4123_) == 0 {
                        v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
                        lean_inc(v_a_4124_);
                        lean_dec_ref_known(v___x_4123_, 1);
                        if lean_obj_tag(v_a_4124_) == 1 {
                            v_mvarIds_4125_ = lean_ctor_get(v_a_4124_, 0);
                            lean_inc(v_mvarIds_4125_);
                            lean_dec_ref_known(v_a_4124_, 1);
                            if lean_obj_tag(v_mvarIds_4125_) == 1 {
                                v_tail_4126_ = lean_ctor_get(v_mvarIds_4125_, 1);
                                if lean_obj_tag(v_tail_4126_) == 0 {
                                    lean_dec(v_goal_3715_);
                                    v_head_4127_ = lean_ctor_get(v_mvarIds_4125_, 0);
                                    lean_inc(v_head_4127_);
                                    lean_dec_ref_known(v_mvarIds_4125_, 2);
                                    v___x_4128_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
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
                                    if lean_obj_tag(v___x_4129_) == 0 {
                                        v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
                                        lean_inc(v_a_4130_);
                                        lean_dec_ref_known(v___x_4129_, 1);
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
                                        lean_dec(v___y_4108_);
                                        lean_dec(v___y_4107_);
                                        v_a_4131_ = lean_ctor_get(v___x_4129_, 0);
                                        v_isSharedCheck_4138_ =
                                            (!lean_is_exclusive(v___x_4129_)) as u8;
                                        if v_isSharedCheck_4138_ == 0 {
                                            v___x_4133_ = v___x_4129_;
                                            v_isShared_4134_ = v_isSharedCheck_4138_;
                                            state = 47;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4131_);
                                            lean_dec(v___x_4129_);
                                            v___x_4133_ = lean_box(0);
                                            v_isShared_4134_ = v_isSharedCheck_4138_;
                                            state = 47;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_mvarIds_4125_, 2);
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
                                lean_dec(v_mvarIds_4125_);
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
                            lean_dec(v_a_4124_);
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
                        lean_dec(v___y_4108_);
                        lean_dec(v___y_4107_);
                        lean_dec(v_goal_3715_);
                        v_a_4139_ = lean_ctor_get(v___x_4123_, 0);
                        v_isSharedCheck_4146_ = (!lean_is_exclusive(v___x_4123_)) as u8;
                        if v_isSharedCheck_4146_ == 0 {
                            v___x_4141_ = v___x_4123_;
                            v_isShared_4142_ = v_isSharedCheck_4146_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_a_4139_);
                            lean_dec(v___x_4123_);
                            v___x_4141_ = lean_box(0);
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
                    v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
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
                    v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
                    v___x_4144_ = v_reuseFailAlloc_4145_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_4144_;
            }
            51 => {
                if lean_obj_tag(v___y_4148_) == 0 {
                    lean_dec(v___y_4149_);
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
                    v_val_4150_ = lean_ctor_get(v___y_4148_, 0);
                    v___x_4151_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21);
                    v___x_4152_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22;
                    lean_inc(v_val_4150_);
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
                    if lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
                        lean_inc(v_a_4154_);
                        lean_dec_ref_known(v___x_4153_, 1);
                        v___x_4155_ = (lean_unbox(v_a_4154_) as u8);
                        lean_dec(v_a_4154_);
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
                            lean_dec_ref_known(v___y_4148_, 1);
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
                        if lean_obj_tag(v___x_4153_) == 0 {
                            v_a_4156_ = lean_ctor_get(v___x_4153_, 0);
                            lean_inc(v_a_4156_);
                            lean_dec_ref_known(v___x_4153_, 1);
                            v___x_4157_ = (lean_unbox(v_a_4156_) as u8);
                            lean_dec(v_a_4156_);
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
                            lean_dec_ref_known(v___y_4148_, 1);
                            lean_dec(v___y_4149_);
                            lean_dec(v_goal_3715_);
                            v_a_4158_ = lean_ctor_get(v___x_4153_, 0);
                            v_isSharedCheck_4165_ = (!lean_is_exclusive(v___x_4153_)) as u8;
                            if v_isSharedCheck_4165_ == 0 {
                                v___x_4160_ = v___x_4153_;
                                v_isShared_4161_ = v_isSharedCheck_4165_;
                                state = 52;
                                continue;
                            } else {
                                lean_inc(v_a_4158_);
                                lean_dec(v___x_4153_);
                                v___x_4160_ = lean_box(0);
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
                    v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
                    v___x_4163_ = v_reuseFailAlloc_4164_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4163_;
            }
            54 => {
                v___x_4168_ = lean_unsigned_to_nat(2);
                v___x_4169_ = l_Lean_Expr_isAppOfArity(v_arg_3828_, v___x_3884_, v___x_4168_);
                if v___x_4169_ == 0 {
                    lean_dec_ref(v_arg_3828_);
                    v___x_4170_ = lean_box(0);
                    v___y_4148_ = v___y_4167_;
                    v___y_4149_ = v___x_4170_;
                    state = 51;
                    continue;
                } else {
                    v___x_4171_ = l_Lean_Expr_appArg_x21(v_arg_3828_);
                    lean_dec_ref(v_arg_3828_);
                    v___x_4172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4172_, 0, v___x_4171_);
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
                    v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
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
    mut v_goal_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4200_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    lean_dec(v___y_4196_);
    lean_dec_ref(v___y_4195_);
    lean_dec(v___y_4194_);
    lean_dec_ref(v___y_4193_);
    lean_dec(v___y_4192_);
    lean_dec_ref(v___y_4191_);
    lean_dec(v___y_4190_);
    lean_dec(v___y_4189_);
    lean_dec_ref(v___y_4188_);
    return v_res_4200_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(
    mut v_goal_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
    mut v_a_4206_: *mut LeanObject,
    mut v_a_4207_: *mut LeanObject,
    mut v_a_4208_: *mut LeanObject,
    mut v_a_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
    mut v_a_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_4201_);
    v___f_4214_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    lean_closure_set(v___f_4214_, 0, v_goal_4201_);
    v___x_4215_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_4201_, v___f_4214_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
    return v___x_4215_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___boxed(
    mut v_goal_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
    mut v_a_4221_: *mut LeanObject,
    mut v_a_4222_: *mut LeanObject,
    mut v_a_4223_: *mut LeanObject,
    mut v_a_4224_: *mut LeanObject,
    mut v_a_4225_: *mut LeanObject,
    mut v_a_4226_: *mut LeanObject,
    mut v_a_4227_: *mut LeanObject,
    mut v_a_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4229_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4227_);
    lean_dec_ref(v_a_4226_);
    lean_dec(v_a_4225_);
    lean_dec_ref(v_a_4224_);
    lean_dec(v_a_4223_);
    lean_dec_ref(v_a_4222_);
    lean_dec(v_a_4221_);
    lean_dec_ref(v_a_4220_);
    lean_dec(v_a_4219_);
    lean_dec(v_a_4218_);
    lean_dec_ref(v_a_4217_);
    return v_res_4229_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(
    mut v_progress_4230_: u8,
    mut v_inst_4231_: *mut LeanObject,
    mut v_a_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    v___x_4245_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_4230_, v_a_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
    return v___x_4245_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___boxed(
    mut v_progress_4246_: *mut LeanObject,
    mut v_inst_4247_: *mut LeanObject,
    mut v_a_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
    mut v___y_4258_: *mut LeanObject,
    mut v___y_4259_: *mut LeanObject,
    mut v___y_4260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_progress_boxed_4261_: u8 = 0;
    let mut v_res_4262_: *mut LeanObject = core::ptr::null_mut();
    v_progress_boxed_4261_ = (lean_unbox(v_progress_4246_) as u8);
    v_res_4262_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(v_progress_boxed_4261_, v_inst_4247_, v_a_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
    lean_dec(v___y_4259_);
    lean_dec_ref(v___y_4258_);
    lean_dec(v___y_4257_);
    lean_dec_ref(v___y_4256_);
    lean_dec(v___y_4255_);
    lean_dec_ref(v___y_4254_);
    lean_dec(v___y_4253_);
    lean_dec_ref(v___y_4252_);
    lean_dec(v___y_4251_);
    lean_dec(v___y_4250_);
    lean_dec_ref(v___y_4249_);
    return v_res_4262_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
}
