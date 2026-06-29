// Lean compiler output
// Module: Lean.Elab.Tactic.Generalize
// Imports: Lean.Meta.Tactic.Generalize Lean.Elab.Binders Lean.Elab.Tactic.Location
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_nat_add, lean_nat_dec_lt,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getId};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Binders::{
    initialize_Lean_Elab_Binders, l_Lean_Elab_Term_addLocalVarInfo,
    runtime_initialize_Lean_Elab_Binders,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_elabTerm, l_Lean_Elab_Tactic_getFVarIds,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_toExpr,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Generalize::{
    initialize_Lean_Meta_Tactic_Generalize, l_Lean_MVarId_generalizeHyp,
    runtime_initialize_Lean_Meta_Tactic_Generalize,
};
pub static l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value) as *mut crate::leanh::LeanObject,11287139806334753087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 71, 101, 110, 101, 114, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value) as *mut crate::leanh::LeanObject,8964278067383008981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 40 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 66 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 66 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(
    mut v_x_1059_: *mut crate::leanh::LeanObject,
    mut v___y_1060_: *mut crate::leanh::LeanObject,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
    mut v___y_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1063_);
    crate::leanh::lean_inc_ref(v___y_1062_);
    crate::leanh::lean_inc(v___y_1061_);
    crate::leanh::lean_inc_ref(v___y_1060_);
    v___x_1069_ = crate::leanh::lean_apply_9(
        v_x_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
        v___y_1065_,
        v___y_1066_,
        v___y_1067_,
        crate::leanh::lean_box(0),
    );
    return v___x_1069_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed(
    mut v_x_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
    mut v___y_1078_: *mut crate::leanh::LeanObject,
    mut v___y_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    crate::leanh::lean_dec(v___y_1072_);
    crate::leanh::lean_dec_ref(v___y_1071_);
    return v_res_1080_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(
    mut v_mvarId_1081_: *mut crate::leanh::LeanObject,
    mut v_x_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1086_);
                crate::leanh::lean_inc_ref(v___y_1085_);
                crate::leanh::lean_inc(v___y_1084_);
                crate::leanh::lean_inc_ref(v___y_1083_);
                v___f_1092_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1092_, 0, v_x_1082_);
                crate::leanh::lean_closure_set(v___f_1092_, 1, v___y_1083_);
                crate::leanh::lean_closure_set(v___f_1092_, 2, v___y_1084_);
                crate::leanh::lean_closure_set(v___f_1092_, 3, v___y_1085_);
                crate::leanh::lean_closure_set(v___f_1092_, 4, v___y_1086_);
                v___x_1093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1081_,
                    v___f_1092_,
                    v___y_1087_,
                    v___y_1088_,
                    v___y_1089_,
                    v___y_1090_,
                );
                if crate::leanh::lean_obj_tag(v___x_1093_) == 0 {
                    return v___x_1093_;
                } else {
                    v_a_1094_ = crate::leanh::lean_ctor_get(v___x_1093_, 0);
                    v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v___x_1093_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1096_ = v___x_1093_;
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1094_);
                        crate::leanh::lean_dec(v___x_1093_);
                        v___x_1096_ = crate::leanh::lean_box(0);
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1097_ == 0 {
                    v___x_1099_ = v___x_1096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
                    v___x_1099_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___boxed(
    mut v_mvarId_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(
            v_mvarId_1102_,
            v_x_1103_,
            v___y_1104_,
            v___y_1105_,
            v___y_1106_,
            v___y_1107_,
            v___y_1108_,
            v___y_1109_,
            v___y_1110_,
            v___y_1111_,
        );
    crate::leanh::lean_dec(v___y_1111_);
    crate::leanh::lean_dec_ref(v___y_1110_);
    crate::leanh::lean_dec(v___y_1109_);
    crate::leanh::lean_dec_ref(v___y_1108_);
    crate::leanh::lean_dec(v___y_1107_);
    crate::leanh::lean_dec_ref(v___y_1106_);
    crate::leanh::lean_dec(v___y_1105_);
    crate::leanh::lean_dec_ref(v___y_1104_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(
    mut v_00_u03b1_1114_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1115_: *mut crate::leanh::LeanObject,
    mut v_x_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(
            v_mvarId_1115_,
            v_x_1116_,
            v___y_1117_,
            v___y_1118_,
            v___y_1119_,
            v___y_1120_,
            v___y_1121_,
            v___y_1122_,
            v___y_1123_,
            v___y_1124_,
        );
    return v___x_1126_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___boxed(
    mut v_00_u03b1_1127_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1128_: *mut crate::leanh::LeanObject,
    mut v_x_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(
        v_00_u03b1_1127_,
        v_mvarId_1128_,
        v_x_1129_,
        v___y_1130_,
        v___y_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
        v___y_1136_,
        v___y_1137_,
    );
    crate::leanh::lean_dec(v___y_1137_);
    crate::leanh::lean_dec_ref(v___y_1136_);
    crate::leanh::lean_dec(v___y_1135_);
    crate::leanh::lean_dec_ref(v___y_1134_);
    crate::leanh::lean_dec(v___y_1133_);
    crate::leanh::lean_dec_ref(v___y_1132_);
    crate::leanh::lean_dec(v___y_1131_);
    crate::leanh::lean_dec_ref(v___y_1130_);
    return v_res_1139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(
    mut v_as_1140_: *mut crate::leanh::LeanObject,
    mut v_sz_1141_: usize,
    mut v_i_1142_: usize,
    mut v_b_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1160_: u8 = 0;
    let mut v_a_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_unused_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
                if v___x_1151_ == 0 {
                    v___x_1152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1152_, 0, v_b_1143_);
                    return v___x_1152_;
                } else {
                    v_array_1153_ = crate::leanh::lean_ctor_get(v_b_1143_, 0);
                    v_start_1154_ = crate::leanh::lean_ctor_get(v_b_1143_, 1);
                    v_stop_1155_ = crate::leanh::lean_ctor_get(v_b_1143_, 2);
                    v___x_1156_ = lean_nat_dec_lt(v_start_1154_, v_stop_1155_);
                    if v___x_1156_ == 0 {
                        v___x_1157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1157_, 0, v_b_1143_);
                        return v___x_1157_;
                    } else {
                        crate::leanh::lean_inc(v_stop_1155_);
                        crate::leanh::lean_inc(v_start_1154_);
                        crate::leanh::lean_inc_ref(v_array_1153_);
                        v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v_b_1143_)) as u8;
                        if v_isSharedCheck_1181_ == 0 {
                            v_unused_1182_ = crate::leanh::lean_ctor_get(v_b_1143_, 2);
                            crate::leanh::lean_dec(v_unused_1182_);
                            v_unused_1183_ = crate::leanh::lean_ctor_get(v_b_1143_, 1);
                            crate::leanh::lean_dec(v_unused_1183_);
                            v_unused_1184_ = crate::leanh::lean_ctor_get(v_b_1143_, 0);
                            crate::leanh::lean_dec(v_unused_1184_);
                            v___x_1159_ = v_b_1143_;
                            v_isShared_1160_ = v_isSharedCheck_1181_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_1143_);
                            v___x_1159_ = crate::leanh::lean_box(0);
                            v_isShared_1160_ = v_isSharedCheck_1181_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_1161_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
                v___x_1162_ = lean_array_fget_borrowed(v_array_1153_, v_start_1154_);
                crate::leanh::lean_inc(v_a_1161_);
                v___x_1163_ = l_Lean_Expr_fvar___override(v_a_1161_);
                crate::leanh::lean_inc(v___x_1162_);
                v___x_1164_ = l_Lean_Elab_Term_addLocalVarInfo(
                    v___x_1162_,
                    v___x_1163_,
                    v___y_1144_,
                    v___y_1145_,
                    v___y_1146_,
                    v___y_1147_,
                    v___y_1148_,
                    v___y_1149_,
                );
                if crate::leanh::lean_obj_tag(v___x_1164_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1164_, 1);
                    v___x_1165_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1166_ = lean_nat_add(v_start_1154_, v___x_1165_);
                    crate::leanh::lean_dec(v_start_1154_);
                    if v_isShared_1160_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1159_, 1, v___x_1166_);
                        v___x_1168_ = v___x_1159_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_array_1153_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1166_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_stop_1155_);
                        v___x_1168_ = v_reuseFailAlloc_1172_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1159_);
                    crate::leanh::lean_dec(v_stop_1155_);
                    crate::leanh::lean_dec(v_start_1154_);
                    crate::leanh::lean_dec_ref(v_array_1153_);
                    v_a_1173_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                    v_isSharedCheck_1180_ = (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                    if v_isSharedCheck_1180_ == 0 {
                        v___x_1175_ = v___x_1164_;
                        v_isShared_1176_ = v_isSharedCheck_1180_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1173_);
                        crate::leanh::lean_dec(v___x_1164_);
                        v___x_1175_ = crate::leanh::lean_box(0);
                        v_isShared_1176_ = v_isSharedCheck_1180_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1169_ = 1usize;
                v___x_1170_ = lean_usize_add(v_i_1142_, v___x_1169_);
                v_i_1142_ = v___x_1170_;
                v_b_1143_ = v___x_1168_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1176_ == 0 {
                    v___x_1178_ = v___x_1175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg___boxed(
    mut v_as_1185_: *mut crate::leanh::LeanObject,
    mut v_sz_1186_: *mut crate::leanh::LeanObject,
    mut v_i_1187_: *mut crate::leanh::LeanObject,
    mut v_b_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
    mut v___y_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1196_: usize = 0;
    let mut v_i_boxed_1197_: usize = 0;
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1196_ = crate::leanh::lean_unbox_usize(v_sz_1186_);
    crate::leanh::lean_dec(v_sz_1186_);
    v_i_boxed_1197_ = crate::leanh::lean_unbox_usize(v_i_1187_);
    crate::leanh::lean_dec(v_i_1187_);
    v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_1185_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
    crate::leanh::lean_dec(v___y_1194_);
    crate::leanh::lean_dec_ref(v___y_1193_);
    crate::leanh::lean_dec(v___y_1192_);
    crate::leanh::lean_dec_ref(v___y_1191_);
    crate::leanh::lean_dec(v___y_1190_);
    crate::leanh::lean_dec_ref(v___y_1189_);
    crate::leanh::lean_dec_ref(v_as_1185_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__0(
    mut v_fst_1199_: *mut crate::leanh::LeanObject,
    mut v_sz_1200_: usize,
    mut v___x_1201_: usize,
    mut v___x_1202_: *mut crate::leanh::LeanObject,
    mut v_snd_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_fst_1199_, v_sz_1200_, v___x_1201_, v___x_1202_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
                if crate::leanh::lean_obj_tag(v___x_1213_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1213_, 1);
                    v___x_1214_ = crate::leanh::lean_box(0);
                    v___x_1215_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1215_, 0, v_snd_1203_);
                    crate::leanh::lean_ctor_set(v___x_1215_, 1, v___x_1214_);
                    v___x_1216_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1215_,
                        v___y_1205_,
                        v___y_1208_,
                        v___y_1209_,
                        v___y_1210_,
                        v___y_1211_,
                    );
                    return v___x_1216_;
                } else {
                    crate::leanh::lean_dec(v_snd_1203_);
                    v_a_1217_ = crate::leanh::lean_ctor_get(v___x_1213_, 0);
                    v_isSharedCheck_1224_ = (!crate::leanh::lean_is_exclusive(v___x_1213_)) as u8;
                    if v_isSharedCheck_1224_ == 0 {
                        v___x_1219_ = v___x_1213_;
                        v_isShared_1220_ = v_isSharedCheck_1224_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1217_);
                        crate::leanh::lean_dec(v___x_1213_);
                        v___x_1219_ = crate::leanh::lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1224_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1220_ == 0 {
                    v___x_1222_ = v___x_1219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
                    v___x_1222_ = v_reuseFailAlloc_1223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed(
    mut v_fst_1225_: *mut crate::leanh::LeanObject,
    mut v_sz_1226_: *mut crate::leanh::LeanObject,
    mut v___x_1227_: *mut crate::leanh::LeanObject,
    mut v___x_1228_: *mut crate::leanh::LeanObject,
    mut v_snd_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1239_: usize = 0;
    let mut v___x_9298__boxed_1240_: usize = 0;
    let mut v_res_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1239_ = crate::leanh::lean_unbox_usize(v_sz_1226_);
    crate::leanh::lean_dec(v_sz_1226_);
    v___x_9298__boxed_1240_ = crate::leanh::lean_unbox_usize(v___x_1227_);
    crate::leanh::lean_dec(v___x_1227_);
    v_res_1241_ = l_Lean_Elab_Tactic_evalGeneralize___lam__0(
        v_fst_1225_,
        v_sz_boxed_1239_,
        v___x_9298__boxed_1240_,
        v___x_1228_,
        v_snd_1229_,
        v___y_1230_,
        v___y_1231_,
        v___y_1232_,
        v___y_1233_,
        v___y_1234_,
        v___y_1235_,
        v___y_1236_,
        v___y_1237_,
    );
    crate::leanh::lean_dec(v___y_1237_);
    crate::leanh::lean_dec_ref(v___y_1236_);
    crate::leanh::lean_dec(v___y_1235_);
    crate::leanh::lean_dec_ref(v___y_1234_);
    crate::leanh::lean_dec(v___y_1233_);
    crate::leanh::lean_dec_ref(v___y_1232_);
    crate::leanh::lean_dec(v___y_1231_);
    crate::leanh::lean_dec_ref(v___y_1230_);
    crate::leanh::lean_dec_ref(v_fst_1225_);
    return v_res_1241_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__1(
    mut v_a_1242_: *mut crate::leanh::LeanObject,
    mut v_snd_1243_: *mut crate::leanh::LeanObject,
    mut v_hyps_1244_: *mut crate::leanh::LeanObject,
    mut v___x_1245_: *mut crate::leanh::LeanObject,
    mut v___x_1246_: u8,
    mut v_fst_1247_: *mut crate::leanh::LeanObject,
    mut v_fst_1248_: *mut crate::leanh::LeanObject,
    mut v___x_1249_: *mut crate::leanh::LeanObject,
    mut v___x_1250_: usize,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1268_: usize = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1260_ = l_Lean_MVarId_generalizeHyp(
                    v_a_1242_,
                    v_snd_1243_,
                    v_hyps_1244_,
                    v___x_1245_,
                    v___x_1246_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                    v___y_1258_,
                );
                if crate::leanh::lean_obj_tag(v___x_1260_) == 0 {
                    v_a_1261_ = crate::leanh::lean_ctor_get(v___x_1260_, 0);
                    crate::leanh::lean_inc(v_a_1261_);
                    crate::leanh::lean_dec_ref_known(v___x_1260_, 1);
                    v_snd_1262_ = crate::leanh::lean_ctor_get(v_a_1261_, 1);
                    crate::leanh::lean_inc(v_snd_1262_);
                    crate::leanh::lean_dec(v_a_1261_);
                    v_fst_1263_ = crate::leanh::lean_ctor_get(v_snd_1262_, 0);
                    crate::leanh::lean_inc(v_fst_1263_);
                    v_snd_1264_ = crate::leanh::lean_ctor_get(v_snd_1262_, 1);
                    crate::leanh::lean_inc_n(v_snd_1264_, 2);
                    crate::leanh::lean_dec(v_snd_1262_);
                    v___x_1265_ = l_Array_append___redArg(v_fst_1247_, v_fst_1248_);
                    v___x_1266_ = lean_array_get_size(v___x_1265_);
                    v___x_1267_ =
                        l_Array_toSubarray___redArg(v___x_1265_, v___x_1249_, v___x_1266_);
                    v_sz_1268_ = lean_array_size(v_fst_1263_);
                    v___x_1269_ = crate::leanh::lean_box_usize(v_sz_1268_);
                    v___x_1270_ = crate::leanh::lean_box_usize(v___x_1250_);
                    v___f_1271_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_1271_, 0, v_fst_1263_);
                    crate::leanh::lean_closure_set(v___f_1271_, 1, v___x_1269_);
                    crate::leanh::lean_closure_set(v___f_1271_, 2, v___x_1270_);
                    crate::leanh::lean_closure_set(v___f_1271_, 3, v___x_1267_);
                    crate::leanh::lean_closure_set(v___f_1271_, 4, v_snd_1264_);
                    v___x_1272_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_snd_1264_, v___f_1271_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
                    return v___x_1272_;
                } else {
                    crate::leanh::lean_dec(v___x_1249_);
                    crate::leanh::lean_dec(v_fst_1247_);
                    v_a_1273_ = crate::leanh::lean_ctor_get(v___x_1260_, 0);
                    v_isSharedCheck_1280_ = (!crate::leanh::lean_is_exclusive(v___x_1260_)) as u8;
                    if v_isSharedCheck_1280_ == 0 {
                        v___x_1275_ = v___x_1260_;
                        v_isShared_1276_ = v_isSharedCheck_1280_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1273_);
                        crate::leanh::lean_dec(v___x_1260_);
                        v___x_1275_ = crate::leanh::lean_box(0);
                        v_isShared_1276_ = v_isSharedCheck_1280_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1276_ == 0 {
                    v___x_1278_ = v___x_1275_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
                    v___x_1278_ = v_reuseFailAlloc_1279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1281_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_1282_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_hyps_1283_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1284_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_1285_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_fst_1286_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_fst_1287_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_1288_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_1289_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1290_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1291_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1292_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1293_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1294_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1295_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1296_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1297_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1298_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_9363__boxed_1299_: u8 = 0;
    let mut v___x_9365__boxed_1300_: usize = 0;
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9363__boxed_1299_ = (crate::leanh::lean_unbox(v___x_1285_) as u8);
    v___x_9365__boxed_1300_ = crate::leanh::lean_unbox_usize(v___x_1289_);
    crate::leanh::lean_dec(v___x_1289_);
    v_res_1301_ = l_Lean_Elab_Tactic_evalGeneralize___lam__1(
        v_a_1281_,
        v_snd_1282_,
        v_hyps_1283_,
        v___x_1284_,
        v___x_9363__boxed_1299_,
        v_fst_1286_,
        v_fst_1287_,
        v___x_1288_,
        v___x_9365__boxed_1300_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
        v___y_1295_,
        v___y_1296_,
        v___y_1297_,
    );
    crate::leanh::lean_dec(v___y_1297_);
    crate::leanh::lean_dec_ref(v___y_1296_);
    crate::leanh::lean_dec(v___y_1295_);
    crate::leanh::lean_dec_ref(v___y_1294_);
    crate::leanh::lean_dec(v___y_1293_);
    crate::leanh::lean_dec_ref(v___y_1292_);
    crate::leanh::lean_dec(v___y_1291_);
    crate::leanh::lean_dec_ref(v___y_1290_);
    crate::leanh::lean_dec(v_fst_1287_);
    crate::leanh::lean_dec_ref(v_hyps_1283_);
    return v_res_1301_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(
    mut v_as_1302_: *mut crate::leanh::LeanObject,
    mut v_sz_1303_: usize,
    mut v_i_1304_: usize,
    mut v_b_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v_fst_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hName_x3f_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hIdents_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: usize = 0;
    let mut v_reuseFailAlloc_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
                if v___x_1315_ == 0 {
                    v___x_1316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1316_, 0, v_b_1305_);
                    return v___x_1316_;
                } else {
                    v_snd_1317_ = crate::leanh::lean_ctor_get(v_b_1305_, 1);
                    v_fst_1318_ = crate::leanh::lean_ctor_get(v_b_1305_, 0);
                    v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v_b_1305_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v___x_1320_ = v_b_1305_;
                        v_isShared_1321_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1317_);
                        crate::leanh::lean_inc(v_fst_1318_);
                        crate::leanh::lean_dec(v_b_1305_);
                        v___x_1320_ = crate::leanh::lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1322_ = crate::leanh::lean_ctor_get(v_snd_1317_, 0);
                v_snd_1323_ = crate::leanh::lean_ctor_get(v_snd_1317_, 1);
                v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v_snd_1317_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1325_ = v_snd_1317_;
                    v_isShared_1326_ = v_isSharedCheck_1377_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1323_);
                    crate::leanh::lean_inc(v_fst_1322_);
                    crate::leanh::lean_dec(v_snd_1317_);
                    v___x_1325_ = crate::leanh::lean_box(0);
                    v_isShared_1326_ = v_isSharedCheck_1377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1327_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_1328_ = lean_array_uget_borrowed(v_as_1302_, v_i_1304_);
                v___x_1369_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1370_ = l_Lean_Syntax_getArg(v_a_1328_, v___x_1369_);
                v___x_1371_ = l_Lean_Syntax_isNone(v___x_1370_);
                if v___x_1371_ == 0 {
                    v___x_1372_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_1369_);
                    crate::leanh::lean_dec(v___x_1370_);
                    crate::leanh::lean_inc(v___x_1372_);
                    v___x_1373_ = lean_array_push(v_fst_1322_, v___x_1372_);
                    v___x_1374_ = l_Lean_Syntax_getId(v___x_1372_);
                    crate::leanh::lean_dec(v___x_1372_);
                    v___x_1375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
                    v_hName_x3f_1330_ = v___x_1375_;
                    v_hIdents_1331_ = v___x_1373_;
                    v___y_1332_ = v___y_1306_;
                    v___y_1333_ = v___y_1307_;
                    v___y_1334_ = v___y_1308_;
                    v___y_1335_ = v___y_1309_;
                    v___y_1336_ = v___y_1310_;
                    v___y_1337_ = v___y_1311_;
                    v___y_1338_ = v___y_1312_;
                    v___y_1339_ = v___y_1313_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1370_);
                    v___x_1376_ = crate::leanh::lean_box(0);
                    v_hName_x3f_1330_ = v___x_1376_;
                    v_hIdents_1331_ = v_fst_1322_;
                    v___y_1332_ = v___y_1306_;
                    v___y_1333_ = v___y_1307_;
                    v___y_1334_ = v___y_1308_;
                    v___y_1335_ = v___y_1309_;
                    v___y_1336_ = v___y_1310_;
                    v___y_1337_ = v___y_1311_;
                    v___y_1338_ = v___y_1312_;
                    v___y_1339_ = v___y_1313_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1340_ = l_Lean_Syntax_getArg(v_a_1328_, v___x_1327_);
                v___x_1341_ = crate::leanh::lean_box(0);
                v___x_1342_ = 0;
                v___x_1343_ = l_Lean_Elab_Tactic_elabTerm(
                    v___x_1340_,
                    v___x_1341_,
                    v___x_1342_,
                    v___y_1332_,
                    v___y_1333_,
                    v___y_1334_,
                    v___y_1335_,
                    v___y_1336_,
                    v___y_1337_,
                    v___y_1338_,
                    v___y_1339_,
                );
                if crate::leanh::lean_obj_tag(v___x_1343_) == 0 {
                    v_a_1344_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                    crate::leanh::lean_inc(v_a_1344_);
                    crate::leanh::lean_dec_ref_known(v___x_1343_, 1);
                    v___x_1345_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1346_ = l_Lean_Syntax_getArg(v_a_1328_, v___x_1345_);
                    crate::leanh::lean_inc(v___x_1346_);
                    v___x_1347_ = lean_array_push(v_fst_1318_, v___x_1346_);
                    v___x_1348_ = l_Lean_Syntax_getId(v___x_1346_);
                    crate::leanh::lean_dec(v___x_1346_);
                    v___x_1349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                    v___x_1350_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1350_, 0, v_a_1344_);
                    crate::leanh::lean_ctor_set(v___x_1350_, 1, v___x_1349_);
                    crate::leanh::lean_ctor_set(v___x_1350_, 2, v_hName_x3f_1330_);
                    v___x_1351_ = lean_array_push(v_snd_1323_, v___x_1350_);
                    if v_isShared_1326_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1325_, 1, v___x_1351_);
                        crate::leanh::lean_ctor_set(v___x_1325_, 0, v_hIdents_1331_);
                        v___x_1353_ = v___x_1325_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_hIdents_1331_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1351_);
                        v___x_1353_ = v_reuseFailAlloc_1360_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_hIdents_1331_);
                    crate::leanh::lean_dec(v_hName_x3f_1330_);
                    crate::leanh::lean_del_object(v___x_1325_);
                    crate::leanh::lean_dec(v_snd_1323_);
                    crate::leanh::lean_del_object(v___x_1320_);
                    crate::leanh::lean_dec(v_fst_1318_);
                    v_a_1361_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                    v_isSharedCheck_1368_ = (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1363_ = v___x_1343_;
                        v_isShared_1364_ = v_isSharedCheck_1368_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1361_);
                        crate::leanh::lean_dec(v___x_1343_);
                        v___x_1363_ = crate::leanh::lean_box(0);
                        v_isShared_1364_ = v_isSharedCheck_1368_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1320_, 1, v___x_1353_);
                    crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1347_);
                    v___x_1355_ = v___x_1320_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1353_);
                    v___x_1355_ = v_reuseFailAlloc_1359_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1356_ = 1usize;
                v___x_1357_ = lean_usize_add(v_i_1304_, v___x_1356_);
                v_i_1304_ = v___x_1357_;
                v_b_1305_ = v___x_1355_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1364_ == 0 {
                    v___x_1366_ = v___x_1363_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0___boxed(
    mut v_as_1379_: *mut crate::leanh::LeanObject,
    mut v_sz_1380_: *mut crate::leanh::LeanObject,
    mut v_i_1381_: *mut crate::leanh::LeanObject,
    mut v_b_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1392_: usize = 0;
    let mut v_i_boxed_1393_: usize = 0;
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1392_ = crate::leanh::lean_unbox_usize(v_sz_1380_);
    crate::leanh::lean_dec(v_sz_1380_);
    v_i_boxed_1393_ = crate::leanh::lean_unbox_usize(v_i_1381_);
    crate::leanh::lean_dec(v_i_1381_);
    v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v_as_1379_, v_sz_boxed_1392_, v_i_boxed_1393_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
    crate::leanh::lean_dec(v___y_1390_);
    crate::leanh::lean_dec_ref(v___y_1389_);
    crate::leanh::lean_dec(v___y_1388_);
    crate::leanh::lean_dec_ref(v___y_1387_);
    crate::leanh::lean_dec(v___y_1386_);
    crate::leanh::lean_dec_ref(v___y_1385_);
    crate::leanh::lean_dec(v___y_1384_);
    crate::leanh::lean_dec_ref(v___y_1383_);
    crate::leanh::lean_dec_ref(v_as_1379_);
    return v_res_1394_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(
    mut v_as_1395_: *mut crate::leanh::LeanObject,
    mut v_sz_1396_: usize,
    mut v_i_1397_: usize,
    mut v_b_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: usize = 0;
    let mut v___x_1412_: usize = 0;
    let mut v_reuseFailAlloc_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = lean_usize_dec_lt(v_i_1397_, v_sz_1396_);
                if v___x_1400_ == 0 {
                    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v_b_1398_);
                    return v___x_1401_;
                } else {
                    v_snd_1402_ = crate::leanh::lean_ctor_get(v_b_1398_, 1);
                    v_isSharedCheck_1420_ = (!crate::leanh::lean_is_exclusive(v_b_1398_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v_unused_1421_ = crate::leanh::lean_ctor_get(v_b_1398_, 0);
                        crate::leanh::lean_dec(v_unused_1421_);
                        v___x_1404_ = v_b_1398_;
                        v_isShared_1405_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1402_);
                        crate::leanh::lean_dec(v_b_1398_);
                        v___x_1404_ = crate::leanh::lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1406_ = crate::leanh::lean_box(0);
                v_a_1415_ = lean_array_uget_borrowed(v_as_1395_, v_i_1397_);
                if crate::leanh::lean_obj_tag(v_a_1415_) == 0 {
                    v_a_1408_ = v_snd_1402_;
                    state = 2;
                    continue;
                } else {
                    v_val_1416_ = crate::leanh::lean_ctor_get(v_a_1415_, 0);
                    v___x_1417_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1416_);
                    if v___x_1417_ == 0 {
                        crate::leanh::lean_inc(v_val_1416_);
                        v___x_1418_ = l_Lean_LocalDecl_toExpr(v_val_1416_);
                        v___x_1419_ = lean_array_push(v_snd_1402_, v___x_1418_);
                        v_a_1408_ = v___x_1419_;
                        state = 2;
                        continue;
                    } else {
                        v_a_1408_ = v_snd_1402_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1404_, 1, v_a_1408_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1406_);
                    v___x_1410_ = v___x_1404_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1408_);
                    v___x_1410_ = v_reuseFailAlloc_1414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1411_ = 1usize;
                v___x_1412_ = lean_usize_add(v_i_1397_, v___x_1411_);
                v_i_1397_ = v___x_1412_;
                v_b_1398_ = v___x_1410_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(
    mut v_as_1422_: *mut crate::leanh::LeanObject,
    mut v_sz_1423_: *mut crate::leanh::LeanObject,
    mut v_i_1424_: *mut crate::leanh::LeanObject,
    mut v_b_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1427_: usize = 0;
    let mut v_i_boxed_1428_: usize = 0;
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1427_ = crate::leanh::lean_unbox_usize(v_sz_1423_);
    crate::leanh::lean_dec(v_sz_1423_);
    v_i_boxed_1428_ = crate::leanh::lean_unbox_usize(v_i_1424_);
    crate::leanh::lean_dec(v_i_1424_);
    v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_1422_, v_sz_boxed_1427_, v_i_boxed_1428_, v_b_1425_);
    crate::leanh::lean_dec_ref(v_as_1422_);
    return v_res_1429_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(
    mut v_as_1430_: *mut crate::leanh::LeanObject,
    mut v_sz_1431_: usize,
    mut v_i_1432_: usize,
    mut v_b_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: usize = 0;
    let mut v___x_1455_: usize = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_unused_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1443_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
                if v___x_1443_ == 0 {
                    v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1444_, 0, v_b_1433_);
                    return v___x_1444_;
                } else {
                    v_snd_1445_ = crate::leanh::lean_ctor_get(v_b_1433_, 1);
                    v_isSharedCheck_1463_ = (!crate::leanh::lean_is_exclusive(v_b_1433_)) as u8;
                    if v_isSharedCheck_1463_ == 0 {
                        v_unused_1464_ = crate::leanh::lean_ctor_get(v_b_1433_, 0);
                        crate::leanh::lean_dec(v_unused_1464_);
                        v___x_1447_ = v_b_1433_;
                        v_isShared_1448_ = v_isSharedCheck_1463_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1445_);
                        crate::leanh::lean_dec(v_b_1433_);
                        v___x_1447_ = crate::leanh::lean_box(0);
                        v_isShared_1448_ = v_isSharedCheck_1463_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1449_ = crate::leanh::lean_box(0);
                v_a_1458_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
                if crate::leanh::lean_obj_tag(v_a_1458_) == 0 {
                    v_a_1451_ = v_snd_1445_;
                    state = 2;
                    continue;
                } else {
                    v_val_1459_ = crate::leanh::lean_ctor_get(v_a_1458_, 0);
                    v___x_1460_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1459_);
                    if v___x_1460_ == 0 {
                        crate::leanh::lean_inc(v_val_1459_);
                        v___x_1461_ = l_Lean_LocalDecl_toExpr(v_val_1459_);
                        v___x_1462_ = lean_array_push(v_snd_1445_, v___x_1461_);
                        v_a_1451_ = v___x_1462_;
                        state = 2;
                        continue;
                    } else {
                        v_a_1451_ = v_snd_1445_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1447_, 1, v_a_1451_);
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1449_);
                    v___x_1453_ = v___x_1447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_a_1451_);
                    v___x_1453_ = v_reuseFailAlloc_1457_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1454_ = 1usize;
                v___x_1455_ = lean_usize_add(v_i_1432_, v___x_1454_);
                v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_1430_, v_sz_1431_, v___x_1455_, v___x_1453_);
                return v___x_1456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7___boxed(
    mut v_as_1465_: *mut crate::leanh::LeanObject,
    mut v_sz_1466_: *mut crate::leanh::LeanObject,
    mut v_i_1467_: *mut crate::leanh::LeanObject,
    mut v_b_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1478_: usize = 0;
    let mut v_i_boxed_1479_: usize = 0;
    let mut v_res_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1478_ = crate::leanh::lean_unbox_usize(v_sz_1466_);
    crate::leanh::lean_dec(v_sz_1466_);
    v_i_boxed_1479_ = crate::leanh::lean_unbox_usize(v_i_1467_);
    crate::leanh::lean_dec(v_i_1467_);
    v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_1465_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
    crate::leanh::lean_dec(v___y_1476_);
    crate::leanh::lean_dec_ref(v___y_1475_);
    crate::leanh::lean_dec(v___y_1474_);
    crate::leanh::lean_dec_ref(v___y_1473_);
    crate::leanh::lean_dec(v___y_1472_);
    crate::leanh::lean_dec_ref(v___y_1471_);
    crate::leanh::lean_dec(v___y_1470_);
    crate::leanh::lean_dec_ref(v___y_1469_);
    crate::leanh::lean_dec_ref(v_as_1465_);
    return v_res_1480_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(
    mut v_init_1481_: *mut crate::leanh::LeanObject,
    mut v_n_1482_: *mut crate::leanh::LeanObject,
    mut v_b_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v_fst_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1513_: u8 = 0;
    let mut v_a_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1521_: u8 = 0;
    let mut v_vs_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1525_: usize = 0;
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1531_: u8 = 0;
    let mut v_fst_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_1482_) == 0 {
                    v_cs_1493_ = crate::leanh::lean_ctor_get(v_n_1482_, 0);
                    v___x_1494_ = crate::leanh::lean_box(0);
                    v___x_1495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 1, v_b_1483_);
                    v_sz_1496_ = lean_array_size(v_cs_1493_);
                    v___x_1497_ = 0usize;
                    v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_1481_, v_cs_1493_, v_sz_1496_, v___x_1497_, v___x_1495_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
                    if crate::leanh::lean_obj_tag(v___x_1498_) == 0 {
                        v_a_1499_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1513_ == 0 {
                            v___x_1501_ = v___x_1498_;
                            v_isShared_1502_ = v_isSharedCheck_1513_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1499_);
                            crate::leanh::lean_dec(v___x_1498_);
                            v___x_1501_ = crate::leanh::lean_box(0);
                            v_isShared_1502_ = v_isSharedCheck_1513_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1514_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1521_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1521_ == 0 {
                            v___x_1516_ = v___x_1498_;
                            v_isShared_1517_ = v_isSharedCheck_1521_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1514_);
                            crate::leanh::lean_dec(v___x_1498_);
                            v___x_1516_ = crate::leanh::lean_box(0);
                            v_isShared_1517_ = v_isSharedCheck_1521_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1522_ = crate::leanh::lean_ctor_get(v_n_1482_, 0);
                    v___x_1523_ = crate::leanh::lean_box(0);
                    v___x_1524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1523_);
                    crate::leanh::lean_ctor_set(v___x_1524_, 1, v_b_1483_);
                    v_sz_1525_ = lean_array_size(v_vs_1522_);
                    v___x_1526_ = 0usize;
                    v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_vs_1522_, v_sz_1525_, v___x_1526_, v___x_1524_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
                    if crate::leanh::lean_obj_tag(v___x_1527_) == 0 {
                        v_a_1528_ = crate::leanh::lean_ctor_get(v___x_1527_, 0);
                        v_isSharedCheck_1542_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1527_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1530_ = v___x_1527_;
                            v_isShared_1531_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1528_);
                            crate::leanh::lean_dec(v___x_1527_);
                            v___x_1530_ = crate::leanh::lean_box(0);
                            v_isShared_1531_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1543_ = crate::leanh::lean_ctor_get(v___x_1527_, 0);
                        v_isSharedCheck_1550_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1527_)) as u8;
                        if v_isSharedCheck_1550_ == 0 {
                            v___x_1545_ = v___x_1527_;
                            v_isShared_1546_ = v_isSharedCheck_1550_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1543_);
                            crate::leanh::lean_dec(v___x_1527_);
                            v___x_1545_ = crate::leanh::lean_box(0);
                            v_isShared_1546_ = v_isSharedCheck_1550_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1503_ = crate::leanh::lean_ctor_get(v_a_1499_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1503_) == 0 {
                    v_snd_1504_ = crate::leanh::lean_ctor_get(v_a_1499_, 1);
                    crate::leanh::lean_inc(v_snd_1504_);
                    crate::leanh::lean_dec(v_a_1499_);
                    v___x_1505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1505_, 0, v_snd_1504_);
                    if v_isShared_1502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1505_);
                        v___x_1507_ = v___x_1501_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
                        v___x_1507_ = v_reuseFailAlloc_1508_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1503_);
                    crate::leanh::lean_dec(v_a_1499_);
                    v_val_1509_ = crate::leanh::lean_ctor_get(v_fst_1503_, 0);
                    crate::leanh::lean_inc(v_val_1509_);
                    crate::leanh::lean_dec_ref_known(v_fst_1503_, 1);
                    if v_isShared_1502_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1501_, 0, v_val_1509_);
                        v___x_1511_ = v___x_1501_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1509_);
                        v___x_1511_ = v_reuseFailAlloc_1512_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1507_;
            }
            3 => {
                return v___x_1511_;
            }
            4 => {
                if v_isShared_1517_ == 0 {
                    v___x_1519_ = v___x_1516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
                    v___x_1519_ = v_reuseFailAlloc_1520_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1519_;
            }
            6 => {
                v_fst_1532_ = crate::leanh::lean_ctor_get(v_a_1528_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1532_) == 0 {
                    v_snd_1533_ = crate::leanh::lean_ctor_get(v_a_1528_, 1);
                    crate::leanh::lean_inc(v_snd_1533_);
                    crate::leanh::lean_dec(v_a_1528_);
                    v___x_1534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1534_, 0, v_snd_1533_);
                    if v_isShared_1531_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1534_);
                        v___x_1536_ = v___x_1530_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
                        v___x_1536_ = v_reuseFailAlloc_1537_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1532_);
                    crate::leanh::lean_dec(v_a_1528_);
                    v_val_1538_ = crate::leanh::lean_ctor_get(v_fst_1532_, 0);
                    crate::leanh::lean_inc(v_val_1538_);
                    crate::leanh::lean_dec_ref_known(v_fst_1532_, 1);
                    if v_isShared_1531_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1530_, 0, v_val_1538_);
                        v___x_1540_ = v___x_1530_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_val_1538_);
                        v___x_1540_ = v_reuseFailAlloc_1541_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1536_;
            }
            8 => {
                return v___x_1540_;
            }
            9 => {
                if v_isShared_1546_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
                    v___x_1548_ = v_reuseFailAlloc_1549_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(
    mut v_init_1551_: *mut crate::leanh::LeanObject,
    mut v_as_1552_: *mut crate::leanh::LeanObject,
    mut v_sz_1553_: usize,
    mut v_i_1554_: usize,
    mut v_b_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
    mut v___y_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: usize = 0;
    let mut v_reuseFailAlloc_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut v_a_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_unused_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1565_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
                if v___x_1565_ == 0 {
                    v___x_1566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1566_, 0, v_b_1555_);
                    return v___x_1566_;
                } else {
                    v_snd_1567_ = crate::leanh::lean_ctor_get(v_b_1555_, 1);
                    v_isSharedCheck_1601_ = (!crate::leanh::lean_is_exclusive(v_b_1555_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v_unused_1602_ = crate::leanh::lean_ctor_get(v_b_1555_, 0);
                        crate::leanh::lean_dec(v_unused_1602_);
                        v___x_1569_ = v_b_1555_;
                        v_isShared_1570_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1567_);
                        crate::leanh::lean_dec(v_b_1555_);
                        v___x_1569_ = crate::leanh::lean_box(0);
                        v_isShared_1570_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1571_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
                crate::leanh::lean_inc(v_snd_1567_);
                v___x_1572_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1551_, v_a_1571_, v_snd_1567_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
                if crate::leanh::lean_obj_tag(v___x_1572_) == 0 {
                    v_a_1573_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1592_ = (!crate::leanh::lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1592_ == 0 {
                        v___x_1575_ = v___x_1572_;
                        v_isShared_1576_ = v_isSharedCheck_1592_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1573_);
                        crate::leanh::lean_dec(v___x_1572_);
                        v___x_1575_ = crate::leanh::lean_box(0);
                        v_isShared_1576_ = v_isSharedCheck_1592_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1569_);
                    crate::leanh::lean_dec(v_snd_1567_);
                    v_a_1593_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1600_ = (!crate::leanh::lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1600_ == 0 {
                        v___x_1595_ = v___x_1572_;
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1593_);
                        crate::leanh::lean_dec(v___x_1572_);
                        v___x_1595_ = crate::leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1573_) == 0 {
                    v___x_1577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1577_, 0, v_a_1573_);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1577_);
                        v___x_1579_ = v___x_1569_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_snd_1567_);
                        v___x_1579_ = v_reuseFailAlloc_1583_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1575_);
                    crate::leanh::lean_dec(v_snd_1567_);
                    v_a_1584_ = crate::leanh::lean_ctor_get(v_a_1573_, 0);
                    crate::leanh::lean_inc(v_a_1584_);
                    crate::leanh::lean_dec_ref_known(v_a_1573_, 1);
                    v___x_1585_ = crate::leanh::lean_box(0);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1569_, 1, v_a_1584_);
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1585_);
                        v___x_1587_ = v___x_1569_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1591_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_a_1584_);
                        v___x_1587_ = v_reuseFailAlloc_1591_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1579_);
                    v___x_1581_ = v___x_1575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
                    v___x_1581_ = v_reuseFailAlloc_1582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1581_;
            }
            5 => {
                v___x_1588_ = 1usize;
                v___x_1589_ = lean_usize_add(v_i_1554_, v___x_1588_);
                v_i_1554_ = v___x_1589_;
                v_b_1555_ = v___x_1587_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1596_ == 0 {
                    v___x_1598_ = v___x_1595_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
                    v___x_1598_ = v_reuseFailAlloc_1599_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6___boxed(
    mut v_init_1603_: *mut crate::leanh::LeanObject,
    mut v_as_1604_: *mut crate::leanh::LeanObject,
    mut v_sz_1605_: *mut crate::leanh::LeanObject,
    mut v_i_1606_: *mut crate::leanh::LeanObject,
    mut v_b_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1617_: usize = 0;
    let mut v_i_boxed_1618_: usize = 0;
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1617_ = crate::leanh::lean_unbox_usize(v_sz_1605_);
    crate::leanh::lean_dec(v_sz_1605_);
    v_i_boxed_1618_ = crate::leanh::lean_unbox_usize(v_i_1606_);
    crate::leanh::lean_dec(v_i_1606_);
    v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_1603_, v_as_1604_, v_sz_boxed_1617_, v_i_boxed_1618_, v_b_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    crate::leanh::lean_dec(v___y_1615_);
    crate::leanh::lean_dec_ref(v___y_1614_);
    crate::leanh::lean_dec(v___y_1613_);
    crate::leanh::lean_dec_ref(v___y_1612_);
    crate::leanh::lean_dec(v___y_1611_);
    crate::leanh::lean_dec_ref(v___y_1610_);
    crate::leanh::lean_dec(v___y_1609_);
    crate::leanh::lean_dec_ref(v___y_1608_);
    crate::leanh::lean_dec_ref(v_as_1604_);
    crate::leanh::lean_dec_ref(v_init_1603_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(
    mut v_init_1620_: *mut crate::leanh::LeanObject,
    mut v_n_1621_: *mut crate::leanh::LeanObject,
    mut v_b_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1620_, v_n_1621_, v_b_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
    crate::leanh::lean_dec(v___y_1630_);
    crate::leanh::lean_dec_ref(v___y_1629_);
    crate::leanh::lean_dec(v___y_1628_);
    crate::leanh::lean_dec_ref(v___y_1627_);
    crate::leanh::lean_dec(v___y_1626_);
    crate::leanh::lean_dec_ref(v___y_1625_);
    crate::leanh::lean_dec(v___y_1624_);
    crate::leanh::lean_dec_ref(v___y_1623_);
    crate::leanh::lean_dec_ref(v_n_1621_);
    crate::leanh::lean_dec_ref(v_init_1620_);
    return v_res_1632_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(
    mut v_as_1633_: *mut crate::leanh::LeanObject,
    mut v_sz_1634_: usize,
    mut v_i_1635_: usize,
    mut v_b_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: usize = 0;
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut v_unused_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1638_ = lean_usize_dec_lt(v_i_1635_, v_sz_1634_);
                if v___x_1638_ == 0 {
                    v___x_1639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1639_, 0, v_b_1636_);
                    return v___x_1639_;
                } else {
                    v_snd_1640_ = crate::leanh::lean_ctor_get(v_b_1636_, 1);
                    v_isSharedCheck_1658_ = (!crate::leanh::lean_is_exclusive(v_b_1636_)) as u8;
                    if v_isSharedCheck_1658_ == 0 {
                        v_unused_1659_ = crate::leanh::lean_ctor_get(v_b_1636_, 0);
                        crate::leanh::lean_dec(v_unused_1659_);
                        v___x_1642_ = v_b_1636_;
                        v_isShared_1643_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1640_);
                        crate::leanh::lean_dec(v_b_1636_);
                        v___x_1642_ = crate::leanh::lean_box(0);
                        v_isShared_1643_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1644_ = crate::leanh::lean_box(0);
                v_a_1653_ = lean_array_uget_borrowed(v_as_1633_, v_i_1635_);
                if crate::leanh::lean_obj_tag(v_a_1653_) == 0 {
                    v_a_1646_ = v_snd_1640_;
                    state = 2;
                    continue;
                } else {
                    v_val_1654_ = crate::leanh::lean_ctor_get(v_a_1653_, 0);
                    v___x_1655_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1654_);
                    if v___x_1655_ == 0 {
                        crate::leanh::lean_inc(v_val_1654_);
                        v___x_1656_ = l_Lean_LocalDecl_toExpr(v_val_1654_);
                        v___x_1657_ = lean_array_push(v_snd_1640_, v___x_1656_);
                        v_a_1646_ = v___x_1657_;
                        state = 2;
                        continue;
                    } else {
                        v_a_1646_ = v_snd_1640_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1642_, 1, v_a_1646_);
                    crate::leanh::lean_ctor_set(v___x_1642_, 0, v___x_1644_);
                    v___x_1648_ = v___x_1642_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1646_);
                    v___x_1648_ = v_reuseFailAlloc_1652_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1649_ = 1usize;
                v___x_1650_ = lean_usize_add(v_i_1635_, v___x_1649_);
                v_i_1635_ = v___x_1650_;
                v_b_1636_ = v___x_1648_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_as_1660_: *mut crate::leanh::LeanObject,
    mut v_sz_1661_: *mut crate::leanh::LeanObject,
    mut v_i_1662_: *mut crate::leanh::LeanObject,
    mut v_b_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1665_: usize = 0;
    let mut v_i_boxed_1666_: usize = 0;
    let mut v_res_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1665_ = crate::leanh::lean_unbox_usize(v_sz_1661_);
    crate::leanh::lean_dec(v_sz_1661_);
    v_i_boxed_1666_ = crate::leanh::lean_unbox_usize(v_i_1662_);
    crate::leanh::lean_dec(v_i_1662_);
    v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_1660_, v_sz_boxed_1665_, v_i_boxed_1666_, v_b_1663_);
    crate::leanh::lean_dec_ref(v_as_1660_);
    return v_res_1667_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(
    mut v_as_1668_: *mut crate::leanh::LeanObject,
    mut v_sz_1669_: usize,
    mut v_i_1670_: usize,
    mut v_b_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: usize = 0;
    let mut v___x_1693_: usize = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1681_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
                if v___x_1681_ == 0 {
                    v___x_1682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v_b_1671_);
                    return v___x_1682_;
                } else {
                    v_snd_1683_ = crate::leanh::lean_ctor_get(v_b_1671_, 1);
                    v_isSharedCheck_1701_ = (!crate::leanh::lean_is_exclusive(v_b_1671_)) as u8;
                    if v_isSharedCheck_1701_ == 0 {
                        v_unused_1702_ = crate::leanh::lean_ctor_get(v_b_1671_, 0);
                        crate::leanh::lean_dec(v_unused_1702_);
                        v___x_1685_ = v_b_1671_;
                        v_isShared_1686_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1683_);
                        crate::leanh::lean_dec(v_b_1671_);
                        v___x_1685_ = crate::leanh::lean_box(0);
                        v_isShared_1686_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1687_ = crate::leanh::lean_box(0);
                v_a_1696_ = lean_array_uget_borrowed(v_as_1668_, v_i_1670_);
                if crate::leanh::lean_obj_tag(v_a_1696_) == 0 {
                    v_a_1689_ = v_snd_1683_;
                    state = 2;
                    continue;
                } else {
                    v_val_1697_ = crate::leanh::lean_ctor_get(v_a_1696_, 0);
                    v___x_1698_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1697_);
                    if v___x_1698_ == 0 {
                        crate::leanh::lean_inc(v_val_1697_);
                        v___x_1699_ = l_Lean_LocalDecl_toExpr(v_val_1697_);
                        v___x_1700_ = lean_array_push(v_snd_1683_, v___x_1699_);
                        v_a_1689_ = v___x_1700_;
                        state = 2;
                        continue;
                    } else {
                        v_a_1689_ = v_snd_1683_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1685_, 1, v_a_1689_);
                    crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1691_ = v___x_1685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_a_1689_);
                    v___x_1691_ = v_reuseFailAlloc_1695_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1692_ = 1usize;
                v___x_1693_ = lean_usize_add(v_i_1670_, v___x_1692_);
                v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_1668_, v_sz_1669_, v___x_1693_, v___x_1691_);
                return v___x_1694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5___boxed(
    mut v_as_1703_: *mut crate::leanh::LeanObject,
    mut v_sz_1704_: *mut crate::leanh::LeanObject,
    mut v_i_1705_: *mut crate::leanh::LeanObject,
    mut v_b_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1716_: usize = 0;
    let mut v_i_boxed_1717_: usize = 0;
    let mut v_res_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1716_ = crate::leanh::lean_unbox_usize(v_sz_1704_);
    crate::leanh::lean_dec(v_sz_1704_);
    v_i_boxed_1717_ = crate::leanh::lean_unbox_usize(v_i_1705_);
    crate::leanh::lean_dec(v_i_1705_);
    v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_1703_, v_sz_boxed_1716_, v_i_boxed_1717_, v_b_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    crate::leanh::lean_dec(v___y_1714_);
    crate::leanh::lean_dec_ref(v___y_1713_);
    crate::leanh::lean_dec(v___y_1712_);
    crate::leanh::lean_dec_ref(v___y_1711_);
    crate::leanh::lean_dec(v___y_1710_);
    crate::leanh::lean_dec_ref(v___y_1709_);
    crate::leanh::lean_dec(v___y_1708_);
    crate::leanh::lean_dec_ref(v___y_1707_);
    crate::leanh::lean_dec_ref(v_as_1703_);
    return v_res_1718_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(
    mut v_t_1719_: *mut crate::leanh::LeanObject,
    mut v_init_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v_a_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v_fst_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_a_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1730_ = crate::leanh::lean_ctor_get(v_t_1719_, 0);
                v_tail_1731_ = crate::leanh::lean_ctor_get(v_t_1719_, 1);
                crate::leanh::lean_inc_ref(v_init_1720_);
                v___x_1732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1720_, v_root_1730_, v_init_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
                crate::leanh::lean_dec_ref(v_init_1720_);
                if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                    v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1735_ = v___x_1732_;
                        v_isShared_1736_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec(v___x_1732_);
                        v___x_1735_ = crate::leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1770_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    v_isSharedCheck_1777_ = (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v___x_1772_ = v___x_1732_;
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1770_);
                        crate::leanh::lean_dec(v___x_1732_);
                        v___x_1772_ = crate::leanh::lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1733_) == 0 {
                    v_a_1737_ = crate::leanh::lean_ctor_get(v_a_1733_, 0);
                    crate::leanh::lean_inc(v_a_1737_);
                    crate::leanh::lean_dec_ref_known(v_a_1733_, 1);
                    if v_isShared_1736_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1735_, 0, v_a_1737_);
                        v___x_1739_ = v___x_1735_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1737_);
                        v___x_1739_ = v_reuseFailAlloc_1740_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1735_);
                    v_a_1741_ = crate::leanh::lean_ctor_get(v_a_1733_, 0);
                    crate::leanh::lean_inc(v_a_1741_);
                    crate::leanh::lean_dec_ref_known(v_a_1733_, 1);
                    v___x_1742_ = crate::leanh::lean_box(0);
                    v___x_1743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    crate::leanh::lean_ctor_set(v___x_1743_, 1, v_a_1741_);
                    v_sz_1744_ = lean_array_size(v_tail_1731_);
                    v___x_1745_ = 0usize;
                    v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_tail_1731_, v_sz_1744_, v___x_1745_, v___x_1743_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
                    if crate::leanh::lean_obj_tag(v___x_1746_) == 0 {
                        v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1749_ = v___x_1746_;
                            v_isShared_1750_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1747_);
                            crate::leanh::lean_dec(v___x_1746_);
                            v___x_1749_ = crate::leanh::lean_box(0);
                            v_isShared_1750_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1768_ == 0 {
                            v___x_1763_ = v___x_1746_;
                            v_isShared_1764_ = v_isSharedCheck_1768_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1761_);
                            crate::leanh::lean_dec(v___x_1746_);
                            v___x_1763_ = crate::leanh::lean_box(0);
                            v_isShared_1764_ = v_isSharedCheck_1768_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1739_;
            }
            3 => {
                v_fst_1751_ = crate::leanh::lean_ctor_get(v_a_1747_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1751_) == 0 {
                    v_snd_1752_ = crate::leanh::lean_ctor_get(v_a_1747_, 1);
                    crate::leanh::lean_inc(v_snd_1752_);
                    crate::leanh::lean_dec(v_a_1747_);
                    if v_isShared_1750_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1749_, 0, v_snd_1752_);
                        v___x_1754_ = v___x_1749_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_snd_1752_);
                        v___x_1754_ = v_reuseFailAlloc_1755_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1751_);
                    crate::leanh::lean_dec(v_a_1747_);
                    v_val_1756_ = crate::leanh::lean_ctor_get(v_fst_1751_, 0);
                    crate::leanh::lean_inc(v_val_1756_);
                    crate::leanh::lean_dec_ref_known(v_fst_1751_, 1);
                    if v_isShared_1750_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1749_, 0, v_val_1756_);
                        v___x_1758_ = v___x_1749_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_val_1756_);
                        v___x_1758_ = v_reuseFailAlloc_1759_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1754_;
            }
            5 => {
                return v___x_1758_;
            }
            6 => {
                if v_isShared_1764_ == 0 {
                    v___x_1766_ = v___x_1763_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
                    v___x_1766_ = v_reuseFailAlloc_1767_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1766_;
            }
            8 => {
                if v_isShared_1773_ == 0 {
                    v___x_1775_ = v___x_1772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
                    v___x_1775_ = v_reuseFailAlloc_1776_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3___boxed(
    mut v_t_1778_: *mut crate::leanh::LeanObject,
    mut v_init_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_1778_, v_init_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
    crate::leanh::lean_dec(v___y_1787_);
    crate::leanh::lean_dec_ref(v___y_1786_);
    crate::leanh::lean_dec(v___y_1785_);
    crate::leanh::lean_dec_ref(v___y_1784_);
    crate::leanh::lean_dec(v___y_1783_);
    crate::leanh::lean_dec_ref(v___y_1782_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    crate::leanh::lean_dec_ref(v_t_1778_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hs_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_1801_ = crate::leanh::lean_ctor_get(v___y_1796_, 2);
    v_decls_1802_ = crate::leanh::lean_ctor_get(v_lctx_1801_, 1);
    v_hs_1803_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0;
    v___x_1804_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_decls_1802_, v_hs_1803_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(
        v___y_1805_,
        v___y_1806_,
        v___y_1807_,
        v___y_1808_,
        v___y_1809_,
        v___y_1810_,
        v___y_1811_,
        v___y_1812_,
    );
    crate::leanh::lean_dec(v___y_1812_);
    crate::leanh::lean_dec_ref(v___y_1811_);
    crate::leanh::lean_dec(v___y_1810_);
    crate::leanh::lean_dec_ref(v___y_1809_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    crate::leanh::lean_dec(v___y_1806_);
    crate::leanh::lean_dec_ref(v___y_1805_);
    return v_res_1814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(
    mut v_sz_1815_: usize,
    mut v_i_1816_: usize,
    mut v_bs_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: u8 = 0;
    let mut v_v_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1818_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
                if v___x_1818_ == 0 {
                    return v_bs_1817_;
                } else {
                    v_v_1819_ = lean_array_uget(v_bs_1817_, v_i_1816_);
                    v___x_1820_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1821_ = lean_array_uset(v_bs_1817_, v_i_1816_, v___x_1820_);
                    v___x_1822_ = l_Lean_Expr_fvarId_x21(v_v_1819_);
                    crate::leanh::lean_dec(v_v_1819_);
                    v___x_1823_ = 1usize;
                    v___x_1824_ = lean_usize_add(v_i_1816_, v___x_1823_);
                    v___x_1825_ = lean_array_uset(v_bs_x27_1821_, v_i_1816_, v___x_1822_);
                    v_i_1816_ = v___x_1824_;
                    v_bs_1817_ = v___x_1825_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4___boxed(
    mut v_sz_1827_: *mut crate::leanh::LeanObject,
    mut v_i_1828_: *mut crate::leanh::LeanObject,
    mut v_bs_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1830_: usize = 0;
    let mut v_i_boxed_1831_: usize = 0;
    let mut v_res_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1830_ = crate::leanh::lean_unbox_usize(v_sz_1827_);
    crate::leanh::lean_dec(v_sz_1827_);
    v_i_boxed_1831_ = crate::leanh::lean_unbox_usize(v_i_1828_);
    crate::leanh::lean_dec(v_i_1828_);
    v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_boxed_1830_, v_i_boxed_1831_, v_bs_1829_);
    return v_res_1832_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__2(
    mut v___x_1833_: *mut crate::leanh::LeanObject,
    mut v_sz_1834_: usize,
    mut v___x_1835_: usize,
    mut v___x_1836_: *mut crate::leanh::LeanObject,
    mut v___x_1837_: *mut crate::leanh::LeanObject,
    mut v_stx_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1885_: usize = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut v_hypotheses_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_a_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v___x_1833_, v_sz_1834_, v___x_1835_, v___x_1836_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
                if crate::leanh::lean_obj_tag(v___x_1848_) == 0 {
                    v_a_1849_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                    crate::leanh::lean_inc(v_a_1849_);
                    crate::leanh::lean_dec_ref_known(v___x_1848_, 1);
                    v_snd_1850_ = crate::leanh::lean_ctor_get(v_a_1849_, 1);
                    crate::leanh::lean_inc(v_snd_1850_);
                    v_fst_1851_ = crate::leanh::lean_ctor_get(v_a_1849_, 0);
                    crate::leanh::lean_inc(v_fst_1851_);
                    crate::leanh::lean_dec(v_a_1849_);
                    v_fst_1852_ = crate::leanh::lean_ctor_get(v_snd_1850_, 0);
                    crate::leanh::lean_inc(v_fst_1852_);
                    v_snd_1853_ = crate::leanh::lean_ctor_get(v_snd_1850_, 1);
                    crate::leanh::lean_inc(v_snd_1853_);
                    crate::leanh::lean_dec(v_snd_1850_);
                    v___x_1880_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1881_ = l_Lean_Syntax_getArg(v_stx_1838_, v___x_1880_);
                    v___x_1882_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1881_);
                    crate::leanh::lean_dec(v___x_1881_);
                    if crate::leanh::lean_obj_tag(v___x_1882_) == 0 {
                        v___x_1883_ =
                            l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(
                                v___y_1839_,
                                v___y_1840_,
                                v___y_1841_,
                                v___y_1842_,
                                v___y_1843_,
                                v___y_1844_,
                                v___y_1845_,
                                v___y_1846_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                            v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                            crate::leanh::lean_inc(v_a_1884_);
                            crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                            v_sz_1885_ = lean_array_size(v_a_1884_);
                            v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_1885_, v___x_1835_, v_a_1884_);
                            v_hyps_1855_ = v___x_1886_;
                            v___y_1856_ = v___y_1839_;
                            v___y_1857_ = v___y_1840_;
                            v___y_1858_ = v___y_1841_;
                            v___y_1859_ = v___y_1842_;
                            v___y_1860_ = v___y_1843_;
                            v___y_1861_ = v___y_1844_;
                            v___y_1862_ = v___y_1845_;
                            v___y_1863_ = v___y_1846_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_1853_);
                            crate::leanh::lean_dec(v_fst_1852_);
                            crate::leanh::lean_dec(v_fst_1851_);
                            crate::leanh::lean_dec(v___x_1837_);
                            v_a_1887_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                            v_isSharedCheck_1894_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                            if v_isSharedCheck_1894_ == 0 {
                                v___x_1889_ = v___x_1883_;
                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1887_);
                                crate::leanh::lean_dec(v___x_1883_);
                                v___x_1889_ = crate::leanh::lean_box(0);
                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_hypotheses_1895_ = crate::leanh::lean_ctor_get(v___x_1882_, 0);
                        crate::leanh::lean_inc_ref(v_hypotheses_1895_);
                        crate::leanh::lean_dec_ref_known(v___x_1882_, 1);
                        v___x_1896_ = l_Lean_Elab_Tactic_getFVarIds(
                            v_hypotheses_1895_,
                            v___y_1839_,
                            v___y_1840_,
                            v___y_1841_,
                            v___y_1842_,
                            v___y_1843_,
                            v___y_1844_,
                            v___y_1845_,
                            v___y_1846_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1896_) == 0 {
                            v_a_1897_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                            crate::leanh::lean_inc(v_a_1897_);
                            crate::leanh::lean_dec_ref_known(v___x_1896_, 1);
                            v_hyps_1855_ = v_a_1897_;
                            v___y_1856_ = v___y_1839_;
                            v___y_1857_ = v___y_1840_;
                            v___y_1858_ = v___y_1841_;
                            v___y_1859_ = v___y_1842_;
                            v___y_1860_ = v___y_1843_;
                            v___y_1861_ = v___y_1844_;
                            v___y_1862_ = v___y_1845_;
                            v___y_1863_ = v___y_1846_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_1853_);
                            crate::leanh::lean_dec(v_fst_1852_);
                            crate::leanh::lean_dec(v_fst_1851_);
                            crate::leanh::lean_dec(v___x_1837_);
                            v_a_1898_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                            v_isSharedCheck_1905_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1896_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1900_ = v___x_1896_;
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1898_);
                                crate::leanh::lean_dec(v___x_1896_);
                                v___x_1900_ = crate::leanh::lean_box(0);
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1837_);
                    v_a_1906_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                    v_isSharedCheck_1913_ = (!crate::leanh::lean_is_exclusive(v___x_1848_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1908_ = v___x_1848_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1906_);
                        crate::leanh::lean_dec(v___x_1848_);
                        v___x_1908_ = crate::leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1864_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1857_,
                    v___y_1860_,
                    v___y_1861_,
                    v___y_1862_,
                    v___y_1863_,
                );
                if crate::leanh::lean_obj_tag(v___x_1864_) == 0 {
                    v_a_1865_ = crate::leanh::lean_ctor_get(v___x_1864_, 0);
                    crate::leanh::lean_inc_n(v_a_1865_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1864_, 1);
                    v___x_1866_ = crate::leanh::lean_box(0);
                    v___x_1867_ = 3;
                    v___x_1868_ = crate::leanh::lean_box((v___x_1867_) as usize);
                    v___x_1869_ = crate::leanh::lean_box_usize(v___x_1835_);
                    v___f_1870_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed
                            as *mut core::ffi::c_void,
                        18,
                        9,
                    );
                    crate::leanh::lean_closure_set(v___f_1870_, 0, v_a_1865_);
                    crate::leanh::lean_closure_set(v___f_1870_, 1, v_snd_1853_);
                    crate::leanh::lean_closure_set(v___f_1870_, 2, v_hyps_1855_);
                    crate::leanh::lean_closure_set(v___f_1870_, 3, v___x_1866_);
                    crate::leanh::lean_closure_set(v___f_1870_, 4, v___x_1868_);
                    crate::leanh::lean_closure_set(v___f_1870_, 5, v_fst_1851_);
                    crate::leanh::lean_closure_set(v___f_1870_, 6, v_fst_1852_);
                    crate::leanh::lean_closure_set(v___f_1870_, 7, v___x_1837_);
                    crate::leanh::lean_closure_set(v___f_1870_, 8, v___x_1869_);
                    v___x_1871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_a_1865_, v___f_1870_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
                    return v___x_1871_;
                } else {
                    crate::leanh::lean_dec_ref(v_hyps_1855_);
                    crate::leanh::lean_dec(v_snd_1853_);
                    crate::leanh::lean_dec(v_fst_1852_);
                    crate::leanh::lean_dec(v_fst_1851_);
                    crate::leanh::lean_dec(v___x_1837_);
                    v_a_1872_ = crate::leanh::lean_ctor_get(v___x_1864_, 0);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v___x_1864_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1874_ = v___x_1864_;
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1872_);
                        crate::leanh::lean_dec(v___x_1864_);
                        v___x_1874_ = crate::leanh::lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1875_ == 0 {
                    v___x_1877_ = v___x_1874_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
                    v___x_1877_ = v_reuseFailAlloc_1878_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1877_;
            }
            4 => {
                if v_isShared_1890_ == 0 {
                    v___x_1892_ = v___x_1889_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1892_;
            }
            6 => {
                if v_isShared_1901_ == 0 {
                    v___x_1903_ = v___x_1900_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1903_;
            }
            8 => {
                if v_isShared_1909_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
                    v___x_1911_ = v_reuseFailAlloc_1912_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed(
    mut v___x_1914_: *mut crate::leanh::LeanObject,
    mut v_sz_1915_: *mut crate::leanh::LeanObject,
    mut v___x_1916_: *mut crate::leanh::LeanObject,
    mut v___x_1917_: *mut crate::leanh::LeanObject,
    mut v___x_1918_: *mut crate::leanh::LeanObject,
    mut v_stx_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1929_: usize = 0;
    let mut v___x_10195__boxed_1930_: usize = 0;
    let mut v_res_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1929_ = crate::leanh::lean_unbox_usize(v_sz_1915_);
    crate::leanh::lean_dec(v_sz_1915_);
    v___x_10195__boxed_1930_ = crate::leanh::lean_unbox_usize(v___x_1916_);
    crate::leanh::lean_dec(v___x_1916_);
    v_res_1931_ = l_Lean_Elab_Tactic_evalGeneralize___lam__2(
        v___x_1914_,
        v_sz_boxed_1929_,
        v___x_10195__boxed_1930_,
        v___x_1917_,
        v___x_1918_,
        v_stx_1919_,
        v___y_1920_,
        v___y_1921_,
        v___y_1922_,
        v___y_1923_,
        v___y_1924_,
        v___y_1925_,
        v___y_1926_,
        v___y_1927_,
    );
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec(v___y_1925_);
    crate::leanh::lean_dec_ref(v___y_1924_);
    crate::leanh::lean_dec(v___y_1923_);
    crate::leanh::lean_dec_ref(v___y_1922_);
    crate::leanh::lean_dec(v___y_1921_);
    crate::leanh::lean_dec_ref(v___y_1920_);
    crate::leanh::lean_dec(v_stx_1919_);
    crate::leanh::lean_dec_ref(v___x_1914_);
    return v_res_1931_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize(
    mut v_stx_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
    mut v_a_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1956_: usize = 0;
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1952_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1953_ = l_Lean_Syntax_getArg(v_stx_1941_, v___x_1952_);
    v___x_1954_ = l_Lean_Syntax_getSepArgs(v___x_1953_);
    crate::leanh::lean_dec(v___x_1953_);
    v___x_1955_ = l_Lean_Elab_Tactic_evalGeneralize___closed__2;
    v_sz_1956_ = lean_array_size(v___x_1954_);
    v___x_1957_ = crate::leanh::lean_box_usize(v_sz_1956_);
    v___x_1958_ = l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1;
    v___f_1959_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1959_, 0, v___x_1954_);
    crate::leanh::lean_closure_set(v___f_1959_, 1, v___x_1957_);
    crate::leanh::lean_closure_set(v___f_1959_, 2, v___x_1958_);
    crate::leanh::lean_closure_set(v___f_1959_, 3, v___x_1955_);
    crate::leanh::lean_closure_set(v___f_1959_, 4, v___x_1951_);
    crate::leanh::lean_closure_set(v___f_1959_, 5, v_stx_1941_);
    v___x_1960_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1959_,
        v_a_1942_,
        v_a_1943_,
        v_a_1944_,
        v_a_1945_,
        v_a_1946_,
        v_a_1947_,
        v_a_1948_,
        v_a_1949_,
    );
    return v___x_1960_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___boxed(
    mut v_stx_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v_a_1965_: *mut crate::leanh::LeanObject,
    mut v_a_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_Elab_Tactic_evalGeneralize(
        v_stx_1961_,
        v_a_1962_,
        v_a_1963_,
        v_a_1964_,
        v_a_1965_,
        v_a_1966_,
        v_a_1967_,
        v_a_1968_,
        v_a_1969_,
    );
    crate::leanh::lean_dec(v_a_1969_);
    crate::leanh::lean_dec_ref(v_a_1968_);
    crate::leanh::lean_dec(v_a_1967_);
    crate::leanh::lean_dec_ref(v_a_1966_);
    crate::leanh::lean_dec(v_a_1965_);
    crate::leanh::lean_dec_ref(v_a_1964_);
    crate::leanh::lean_dec(v_a_1963_);
    crate::leanh::lean_dec_ref(v_a_1962_);
    return v_res_1971_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(
    mut v_as_1972_: *mut crate::leanh::LeanObject,
    mut v_sz_1973_: usize,
    mut v_i_1974_: usize,
    mut v_b_1975_: *mut crate::leanh::LeanObject,
    mut v___y_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_1972_, v_sz_1973_, v_i_1974_, v_b_1975_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
    return v___x_1985_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(
    mut v_as_1986_: *mut crate::leanh::LeanObject,
    mut v_sz_1987_: *mut crate::leanh::LeanObject,
    mut v_i_1988_: *mut crate::leanh::LeanObject,
    mut v_b_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1999_: usize = 0;
    let mut v_i_boxed_2000_: usize = 0;
    let mut v_res_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1999_ = crate::leanh::lean_unbox_usize(v_sz_1987_);
    crate::leanh::lean_dec(v_sz_1987_);
    v_i_boxed_2000_ = crate::leanh::lean_unbox_usize(v_i_1988_);
    crate::leanh::lean_dec(v_i_1988_);
    v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_1986_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
    crate::leanh::lean_dec(v___y_1997_);
    crate::leanh::lean_dec_ref(v___y_1996_);
    crate::leanh::lean_dec(v___y_1995_);
    crate::leanh::lean_dec_ref(v___y_1994_);
    crate::leanh::lean_dec(v___y_1993_);
    crate::leanh::lean_dec_ref(v___y_1992_);
    crate::leanh::lean_dec(v___y_1991_);
    crate::leanh::lean_dec_ref(v___y_1990_);
    crate::leanh::lean_dec_ref(v_as_1986_);
    return v_res_2001_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(
    mut v_as_2002_: *mut crate::leanh::LeanObject,
    mut v_sz_2003_: usize,
    mut v_i_2004_: usize,
    mut v_b_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
    mut v___y_2010_: *mut crate::leanh::LeanObject,
    mut v___y_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_2002_, v_sz_2003_, v_i_2004_, v_b_2005_);
    return v___x_2015_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(
    mut v_as_2016_: *mut crate::leanh::LeanObject,
    mut v_sz_2017_: *mut crate::leanh::LeanObject,
    mut v_i_2018_: *mut crate::leanh::LeanObject,
    mut v_b_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
    mut v___y_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2029_: usize = 0;
    let mut v_i_boxed_2030_: usize = 0;
    let mut v_res_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2029_ = crate::leanh::lean_unbox_usize(v_sz_2017_);
    crate::leanh::lean_dec(v_sz_2017_);
    v_i_boxed_2030_ = crate::leanh::lean_unbox_usize(v_i_2018_);
    crate::leanh::lean_dec(v_i_2018_);
    v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_2016_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
    crate::leanh::lean_dec(v___y_2027_);
    crate::leanh::lean_dec_ref(v___y_2026_);
    crate::leanh::lean_dec(v___y_2025_);
    crate::leanh::lean_dec_ref(v___y_2024_);
    crate::leanh::lean_dec(v___y_2023_);
    crate::leanh::lean_dec_ref(v___y_2022_);
    crate::leanh::lean_dec(v___y_2021_);
    crate::leanh::lean_dec_ref(v___y_2020_);
    crate::leanh::lean_dec_ref(v_as_2016_);
    return v_res_2031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(
    mut v_as_2032_: *mut crate::leanh::LeanObject,
    mut v_sz_2033_: usize,
    mut v_i_2034_: usize,
    mut v_b_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_2032_, v_sz_2033_, v_i_2034_, v_b_2035_);
    return v___x_2045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(
    mut v_as_2046_: *mut crate::leanh::LeanObject,
    mut v_sz_2047_: *mut crate::leanh::LeanObject,
    mut v_i_2048_: *mut crate::leanh::LeanObject,
    mut v_b_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2059_: usize = 0;
    let mut v_i_boxed_2060_: usize = 0;
    let mut v_res_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2059_ = crate::leanh::lean_unbox_usize(v_sz_2047_);
    crate::leanh::lean_dec(v_sz_2047_);
    v_i_boxed_2060_ = crate::leanh::lean_unbox_usize(v_i_2048_);
    crate::leanh::lean_dec(v_i_2048_);
    v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_2046_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
    crate::leanh::lean_dec(v___y_2057_);
    crate::leanh::lean_dec_ref(v___y_2056_);
    crate::leanh::lean_dec(v___y_2055_);
    crate::leanh::lean_dec_ref(v___y_2054_);
    crate::leanh::lean_dec(v___y_2053_);
    crate::leanh::lean_dec_ref(v___y_2052_);
    crate::leanh::lean_dec(v___y_2051_);
    crate::leanh::lean_dec_ref(v___y_2050_);
    crate::leanh::lean_dec_ref(v_as_2046_);
    return v_res_2061_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2080_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4;
    v___x_2081_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7;
    v___x_2082_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalGeneralize___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2079_,
        v___x_2080_,
        v___x_2081_,
        v___x_2082_,
    );
    return v___x_2083_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___boxed(
    mut v_a_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
    return v_res_2085_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7;
    v___x_2113_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6;
    v___x_2114_ = l_Lean_addBuiltinDeclarationRanges(v___x_2112_, v___x_2113_);
    return v___x_2114_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(
    mut v_a_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
    return v_res_2116_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Generalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Generalize(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Generalize(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Generalize(builtin);
}
