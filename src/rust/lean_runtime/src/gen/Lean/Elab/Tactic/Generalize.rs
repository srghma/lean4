// Lean compiler output
// Module: Lean.Elab.Tactic.Generalize
// Imports: Lean.Meta.Tactic.Generalize Lean.Elab.Binders Lean.Elab.Tactic.Location
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getId};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_box_usize, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalGeneralize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value) as *mut LeanObject,11287139806334753087 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 71, 101, 110, 101, 114, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value) as *mut LeanObject,8964278067383008981 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 40 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(
    mut v_x_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
    mut v___y_1066_: *mut LeanObject,
    mut v___y_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1063_);
    lean_inc_ref(v___y_1062_);
    lean_inc(v___y_1061_);
    lean_inc_ref(v___y_1060_);
    v___x_1069_ = lean_apply_9(
        v_x_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
        v___y_1065_,
        v___y_1066_,
        v___y_1067_,
        lean_box(0),
    );
    return v___x_1069_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed(
    mut v_x_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
    mut v___y_1075_: *mut LeanObject,
    mut v___y_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
    mut v___y_1078_: *mut LeanObject,
    mut v___y_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1080_: *mut LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
    lean_dec(v___y_1074_);
    lean_dec_ref(v___y_1073_);
    lean_dec(v___y_1072_);
    lean_dec_ref(v___y_1071_);
    return v_res_1080_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(
    mut v_mvarId_1081_: *mut LeanObject,
    mut v_x_1082_: *mut LeanObject,
    mut v___y_1083_: *mut LeanObject,
    mut v___y_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
    mut v___y_1087_: *mut LeanObject,
    mut v___y_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1086_);
                lean_inc_ref(v___y_1085_);
                lean_inc(v___y_1084_);
                lean_inc_ref(v___y_1083_);
                v___f_1092_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_1092_, 0, v_x_1082_);
                lean_closure_set(v___f_1092_, 1, v___y_1083_);
                lean_closure_set(v___f_1092_, 2, v___y_1084_);
                lean_closure_set(v___f_1092_, 3, v___y_1085_);
                lean_closure_set(v___f_1092_, 4, v___y_1086_);
                v___x_1093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1081_,
                    v___f_1092_,
                    v___y_1087_,
                    v___y_1088_,
                    v___y_1089_,
                    v___y_1090_,
                );
                if lean_obj_tag(v___x_1093_) == 0 {
                    return v___x_1093_;
                } else {
                    v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
                    v_isSharedCheck_1101_ = (!lean_is_exclusive(v___x_1093_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1096_ = v___x_1093_;
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1094_);
                        lean_dec(v___x_1093_);
                        v___x_1096_ = lean_box(0);
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
                    v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
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
    mut v_mvarId_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
    mut v___y_1104_: *mut LeanObject,
    mut v___y_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1111_);
    lean_dec_ref(v___y_1110_);
    lean_dec(v___y_1109_);
    lean_dec_ref(v___y_1108_);
    lean_dec(v___y_1107_);
    lean_dec_ref(v___y_1106_);
    lean_dec(v___y_1105_);
    lean_dec_ref(v___y_1104_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(
    mut v_00_u03b1_1114_: *mut LeanObject,
    mut v_mvarId_1115_: *mut LeanObject,
    mut v_x_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1127_: *mut LeanObject,
    mut v_mvarId_1128_: *mut LeanObject,
    mut v_x_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1139_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1137_);
    lean_dec_ref(v___y_1136_);
    lean_dec(v___y_1135_);
    lean_dec_ref(v___y_1134_);
    lean_dec(v___y_1133_);
    lean_dec_ref(v___y_1132_);
    lean_dec(v___y_1131_);
    lean_dec_ref(v___y_1130_);
    return v_res_1139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(
    mut v_as_1140_: *mut LeanObject,
    mut v_sz_1141_: usize,
    mut v_i_1142_: usize,
    mut v_b_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
    mut v___y_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1160_: u8 = 0;
    let mut v_a_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v_reuseFailAlloc_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_unused_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
                if v___x_1151_ == 0 {
                    v___x_1152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1152_, 0, v_b_1143_);
                    return v___x_1152_;
                } else {
                    v_array_1153_ = lean_ctor_get(v_b_1143_, 0);
                    v_start_1154_ = lean_ctor_get(v_b_1143_, 1);
                    v_stop_1155_ = lean_ctor_get(v_b_1143_, 2);
                    v___x_1156_ = lean_nat_dec_lt(v_start_1154_, v_stop_1155_);
                    if v___x_1156_ == 0 {
                        v___x_1157_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1157_, 0, v_b_1143_);
                        return v___x_1157_;
                    } else {
                        lean_inc(v_stop_1155_);
                        lean_inc(v_start_1154_);
                        lean_inc_ref(v_array_1153_);
                        v_isSharedCheck_1181_ = (!lean_is_exclusive(v_b_1143_)) as u8;
                        if v_isSharedCheck_1181_ == 0 {
                            v_unused_1182_ = lean_ctor_get(v_b_1143_, 2);
                            lean_dec(v_unused_1182_);
                            v_unused_1183_ = lean_ctor_get(v_b_1143_, 1);
                            lean_dec(v_unused_1183_);
                            v_unused_1184_ = lean_ctor_get(v_b_1143_, 0);
                            lean_dec(v_unused_1184_);
                            v___x_1159_ = v_b_1143_;
                            v_isShared_1160_ = v_isSharedCheck_1181_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_1143_);
                            v___x_1159_ = lean_box(0);
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
                lean_inc(v_a_1161_);
                v___x_1163_ = l_Lean_Expr_fvar___override(v_a_1161_);
                lean_inc(v___x_1162_);
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
                if lean_obj_tag(v___x_1164_) == 0 {
                    lean_dec_ref_known(v___x_1164_, 1);
                    v___x_1165_ = lean_unsigned_to_nat(1);
                    v___x_1166_ = lean_nat_add(v_start_1154_, v___x_1165_);
                    lean_dec(v_start_1154_);
                    if v_isShared_1160_ == 0 {
                        lean_ctor_set(v___x_1159_, 1, v___x_1166_);
                        v___x_1168_ = v___x_1159_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_array_1153_);
                        lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1166_);
                        lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_stop_1155_);
                        v___x_1168_ = v_reuseFailAlloc_1172_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1159_);
                    lean_dec(v_stop_1155_);
                    lean_dec(v_start_1154_);
                    lean_dec_ref(v_array_1153_);
                    v_a_1173_ = lean_ctor_get(v___x_1164_, 0);
                    v_isSharedCheck_1180_ = (!lean_is_exclusive(v___x_1164_)) as u8;
                    if v_isSharedCheck_1180_ == 0 {
                        v___x_1175_ = v___x_1164_;
                        v_isShared_1176_ = v_isSharedCheck_1180_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1173_);
                        lean_dec(v___x_1164_);
                        v___x_1175_ = lean_box(0);
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
                    v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
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
    mut v_as_1185_: *mut LeanObject,
    mut v_sz_1186_: *mut LeanObject,
    mut v_i_1187_: *mut LeanObject,
    mut v_b_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
    mut v___y_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1196_: usize = 0;
    let mut v_i_boxed_1197_: usize = 0;
    let mut v_res_1198_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1186_);
    lean_dec(v_sz_1186_);
    v_i_boxed_1197_ = lean_unbox_usize(v_i_1187_);
    lean_dec(v_i_1187_);
    v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_1185_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
    lean_dec(v___y_1194_);
    lean_dec_ref(v___y_1193_);
    lean_dec(v___y_1192_);
    lean_dec_ref(v___y_1191_);
    lean_dec(v___y_1190_);
    lean_dec_ref(v___y_1189_);
    lean_dec_ref(v_as_1185_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__0(
    mut v_fst_1199_: *mut LeanObject,
    mut v_sz_1200_: usize,
    mut v___x_1201_: usize,
    mut v___x_1202_: *mut LeanObject,
    mut v_snd_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_fst_1199_, v_sz_1200_, v___x_1201_, v___x_1202_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
                if lean_obj_tag(v___x_1213_) == 0 {
                    lean_dec_ref_known(v___x_1213_, 1);
                    v___x_1214_ = lean_box(0);
                    v___x_1215_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1215_, 0, v_snd_1203_);
                    lean_ctor_set(v___x_1215_, 1, v___x_1214_);
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
                    lean_dec(v_snd_1203_);
                    v_a_1217_ = lean_ctor_get(v___x_1213_, 0);
                    v_isSharedCheck_1224_ = (!lean_is_exclusive(v___x_1213_)) as u8;
                    if v_isSharedCheck_1224_ == 0 {
                        v___x_1219_ = v___x_1213_;
                        v_isShared_1220_ = v_isSharedCheck_1224_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1217_);
                        lean_dec(v___x_1213_);
                        v___x_1219_ = lean_box(0);
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
                    v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
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
    mut v_fst_1225_: *mut LeanObject,
    mut v_sz_1226_: *mut LeanObject,
    mut v___x_1227_: *mut LeanObject,
    mut v___x_1228_: *mut LeanObject,
    mut v_snd_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1239_: usize = 0;
    let mut v___x_9298__boxed_1240_: usize = 0;
    let mut v_res_1241_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1239_ = lean_unbox_usize(v_sz_1226_);
    lean_dec(v_sz_1226_);
    v___x_9298__boxed_1240_ = lean_unbox_usize(v___x_1227_);
    lean_dec(v___x_1227_);
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
    lean_dec(v___y_1237_);
    lean_dec_ref(v___y_1236_);
    lean_dec(v___y_1235_);
    lean_dec_ref(v___y_1234_);
    lean_dec(v___y_1233_);
    lean_dec_ref(v___y_1232_);
    lean_dec(v___y_1231_);
    lean_dec_ref(v___y_1230_);
    lean_dec_ref(v_fst_1225_);
    return v_res_1241_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__1(
    mut v_a_1242_: *mut LeanObject,
    mut v_snd_1243_: *mut LeanObject,
    mut v_hyps_1244_: *mut LeanObject,
    mut v___x_1245_: *mut LeanObject,
    mut v___x_1246_: u8,
    mut v_fst_1247_: *mut LeanObject,
    mut v_fst_1248_: *mut LeanObject,
    mut v___x_1249_: *mut LeanObject,
    mut v___x_1250_: usize,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1268_: usize = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1260_) == 0 {
                    v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
                    lean_inc(v_a_1261_);
                    lean_dec_ref_known(v___x_1260_, 1);
                    v_snd_1262_ = lean_ctor_get(v_a_1261_, 1);
                    lean_inc(v_snd_1262_);
                    lean_dec(v_a_1261_);
                    v_fst_1263_ = lean_ctor_get(v_snd_1262_, 0);
                    lean_inc(v_fst_1263_);
                    v_snd_1264_ = lean_ctor_get(v_snd_1262_, 1);
                    lean_inc_n(v_snd_1264_, 2);
                    lean_dec(v_snd_1262_);
                    v___x_1265_ = l_Array_append___redArg(v_fst_1247_, v_fst_1248_);
                    v___x_1266_ = lean_array_get_size(v___x_1265_);
                    v___x_1267_ =
                        l_Array_toSubarray___redArg(v___x_1265_, v___x_1249_, v___x_1266_);
                    v_sz_1268_ = lean_array_size(v_fst_1263_);
                    v___x_1269_ = lean_box_usize(v_sz_1268_);
                    v___x_1270_ = lean_box_usize(v___x_1250_);
                    v___f_1271_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    lean_closure_set(v___f_1271_, 0, v_fst_1263_);
                    lean_closure_set(v___f_1271_, 1, v___x_1269_);
                    lean_closure_set(v___f_1271_, 2, v___x_1270_);
                    lean_closure_set(v___f_1271_, 3, v___x_1267_);
                    lean_closure_set(v___f_1271_, 4, v_snd_1264_);
                    v___x_1272_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_snd_1264_, v___f_1271_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
                    return v___x_1272_;
                } else {
                    lean_dec(v___x_1249_);
                    lean_dec(v_fst_1247_);
                    v_a_1273_ = lean_ctor_get(v___x_1260_, 0);
                    v_isSharedCheck_1280_ = (!lean_is_exclusive(v___x_1260_)) as u8;
                    if v_isSharedCheck_1280_ == 0 {
                        v___x_1275_ = v___x_1260_;
                        v_isShared_1276_ = v_isSharedCheck_1280_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1273_);
                        lean_dec(v___x_1260_);
                        v___x_1275_ = lean_box(0);
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
                    v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1281_: *mut LeanObject = *_args.add(0);
    let mut v_snd_1282_: *mut LeanObject = *_args.add(1);
    let mut v_hyps_1283_: *mut LeanObject = *_args.add(2);
    let mut v___x_1284_: *mut LeanObject = *_args.add(3);
    let mut v___x_1285_: *mut LeanObject = *_args.add(4);
    let mut v_fst_1286_: *mut LeanObject = *_args.add(5);
    let mut v_fst_1287_: *mut LeanObject = *_args.add(6);
    let mut v___x_1288_: *mut LeanObject = *_args.add(7);
    let mut v___x_1289_: *mut LeanObject = *_args.add(8);
    let mut v___y_1290_: *mut LeanObject = *_args.add(9);
    let mut v___y_1291_: *mut LeanObject = *_args.add(10);
    let mut v___y_1292_: *mut LeanObject = *_args.add(11);
    let mut v___y_1293_: *mut LeanObject = *_args.add(12);
    let mut v___y_1294_: *mut LeanObject = *_args.add(13);
    let mut v___y_1295_: *mut LeanObject = *_args.add(14);
    let mut v___y_1296_: *mut LeanObject = *_args.add(15);
    let mut v___y_1297_: *mut LeanObject = *_args.add(16);
    let mut v___y_1298_: *mut LeanObject = *_args.add(17);
    let mut v___x_9363__boxed_1299_: u8 = 0;
    let mut v___x_9365__boxed_1300_: usize = 0;
    let mut v_res_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_9363__boxed_1299_ = (lean_unbox(v___x_1285_) as u8);
    v___x_9365__boxed_1300_ = lean_unbox_usize(v___x_1289_);
    lean_dec(v___x_1289_);
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
    lean_dec(v___y_1297_);
    lean_dec_ref(v___y_1296_);
    lean_dec(v___y_1295_);
    lean_dec_ref(v___y_1294_);
    lean_dec(v___y_1293_);
    lean_dec_ref(v___y_1292_);
    lean_dec(v___y_1291_);
    lean_dec_ref(v___y_1290_);
    lean_dec(v_fst_1287_);
    lean_dec_ref(v_hyps_1283_);
    return v_res_1301_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(
    mut v_as_1302_: *mut LeanObject,
    mut v_sz_1303_: usize,
    mut v_i_1304_: usize,
    mut v_b_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v_fst_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hName_x3f_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hIdents_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: usize = 0;
    let mut v_reuseFailAlloc_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
                if v___x_1315_ == 0 {
                    v___x_1316_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1316_, 0, v_b_1305_);
                    return v___x_1316_;
                } else {
                    v_snd_1317_ = lean_ctor_get(v_b_1305_, 1);
                    v_fst_1318_ = lean_ctor_get(v_b_1305_, 0);
                    v_isSharedCheck_1378_ = (!lean_is_exclusive(v_b_1305_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v___x_1320_ = v_b_1305_;
                        v_isShared_1321_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1317_);
                        lean_inc(v_fst_1318_);
                        lean_dec(v_b_1305_);
                        v___x_1320_ = lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1322_ = lean_ctor_get(v_snd_1317_, 0);
                v_snd_1323_ = lean_ctor_get(v_snd_1317_, 1);
                v_isSharedCheck_1377_ = (!lean_is_exclusive(v_snd_1317_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1325_ = v_snd_1317_;
                    v_isShared_1326_ = v_isSharedCheck_1377_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1323_);
                    lean_inc(v_fst_1322_);
                    lean_dec(v_snd_1317_);
                    v___x_1325_ = lean_box(0);
                    v_isShared_1326_ = v_isSharedCheck_1377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1327_ = lean_unsigned_to_nat(1);
                v_a_1328_ = lean_array_uget_borrowed(v_as_1302_, v_i_1304_);
                v___x_1369_ = lean_unsigned_to_nat(0);
                v___x_1370_ = l_Lean_Syntax_getArg(v_a_1328_, v___x_1369_);
                v___x_1371_ = l_Lean_Syntax_isNone(v___x_1370_);
                if v___x_1371_ == 0 {
                    v___x_1372_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_1369_);
                    lean_dec(v___x_1370_);
                    lean_inc(v___x_1372_);
                    v___x_1373_ = lean_array_push(v_fst_1322_, v___x_1372_);
                    v___x_1374_ = l_Lean_Syntax_getId(v___x_1372_);
                    lean_dec(v___x_1372_);
                    v___x_1375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1375_, 0, v___x_1374_);
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
                    lean_dec(v___x_1370_);
                    v___x_1376_ = lean_box(0);
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
                v___x_1341_ = lean_box(0);
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
                if lean_obj_tag(v___x_1343_) == 0 {
                    v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
                    lean_inc(v_a_1344_);
                    lean_dec_ref_known(v___x_1343_, 1);
                    v___x_1345_ = lean_unsigned_to_nat(3);
                    v___x_1346_ = l_Lean_Syntax_getArg(v_a_1328_, v___x_1345_);
                    lean_inc(v___x_1346_);
                    v___x_1347_ = lean_array_push(v_fst_1318_, v___x_1346_);
                    v___x_1348_ = l_Lean_Syntax_getId(v___x_1346_);
                    lean_dec(v___x_1346_);
                    v___x_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                    v___x_1350_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1350_, 0, v_a_1344_);
                    lean_ctor_set(v___x_1350_, 1, v___x_1349_);
                    lean_ctor_set(v___x_1350_, 2, v_hName_x3f_1330_);
                    v___x_1351_ = lean_array_push(v_snd_1323_, v___x_1350_);
                    if v_isShared_1326_ == 0 {
                        lean_ctor_set(v___x_1325_, 1, v___x_1351_);
                        lean_ctor_set(v___x_1325_, 0, v_hIdents_1331_);
                        v___x_1353_ = v___x_1325_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_hIdents_1331_);
                        lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1351_);
                        v___x_1353_ = v_reuseFailAlloc_1360_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_hIdents_1331_);
                    lean_dec(v_hName_x3f_1330_);
                    lean_del_object(v___x_1325_);
                    lean_dec(v_snd_1323_);
                    lean_del_object(v___x_1320_);
                    lean_dec(v_fst_1318_);
                    v_a_1361_ = lean_ctor_get(v___x_1343_, 0);
                    v_isSharedCheck_1368_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1363_ = v___x_1343_;
                        v_isShared_1364_ = v_isSharedCheck_1368_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1361_);
                        lean_dec(v___x_1343_);
                        v___x_1363_ = lean_box(0);
                        v_isShared_1364_ = v_isSharedCheck_1368_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1321_ == 0 {
                    lean_ctor_set(v___x_1320_, 1, v___x_1353_);
                    lean_ctor_set(v___x_1320_, 0, v___x_1347_);
                    v___x_1355_ = v___x_1320_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1347_);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1353_);
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
                    v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
    mut v_as_1379_: *mut LeanObject,
    mut v_sz_1380_: *mut LeanObject,
    mut v_i_1381_: *mut LeanObject,
    mut v_b_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1392_: usize = 0;
    let mut v_i_boxed_1393_: usize = 0;
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1392_ = lean_unbox_usize(v_sz_1380_);
    lean_dec(v_sz_1380_);
    v_i_boxed_1393_ = lean_unbox_usize(v_i_1381_);
    lean_dec(v_i_1381_);
    v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v_as_1379_, v_sz_boxed_1392_, v_i_boxed_1393_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
    lean_dec(v___y_1390_);
    lean_dec_ref(v___y_1389_);
    lean_dec(v___y_1388_);
    lean_dec_ref(v___y_1387_);
    lean_dec(v___y_1386_);
    lean_dec_ref(v___y_1385_);
    lean_dec(v___y_1384_);
    lean_dec_ref(v___y_1383_);
    lean_dec_ref(v_as_1379_);
    return v_res_1394_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(
    mut v_as_1395_: *mut LeanObject,
    mut v_sz_1396_: usize,
    mut v_i_1397_: usize,
    mut v_b_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: usize = 0;
    let mut v___x_1412_: usize = 0;
    let mut v_reuseFailAlloc_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = lean_usize_dec_lt(v_i_1397_, v_sz_1396_);
                if v___x_1400_ == 0 {
                    v___x_1401_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1401_, 0, v_b_1398_);
                    return v___x_1401_;
                } else {
                    v_snd_1402_ = lean_ctor_get(v_b_1398_, 1);
                    v_isSharedCheck_1420_ = (!lean_is_exclusive(v_b_1398_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v_unused_1421_ = lean_ctor_get(v_b_1398_, 0);
                        lean_dec(v_unused_1421_);
                        v___x_1404_ = v_b_1398_;
                        v_isShared_1405_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1402_);
                        lean_dec(v_b_1398_);
                        v___x_1404_ = lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1406_ = lean_box(0);
                v_a_1415_ = lean_array_uget_borrowed(v_as_1395_, v_i_1397_);
                if lean_obj_tag(v_a_1415_) == 0 {
                    v_a_1408_ = v_snd_1402_;
                    state = 2;
                    continue;
                } else {
                    v_val_1416_ = lean_ctor_get(v_a_1415_, 0);
                    v___x_1417_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1416_);
                    if v___x_1417_ == 0 {
                        lean_inc(v_val_1416_);
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
                    lean_ctor_set(v___x_1404_, 1, v_a_1408_);
                    lean_ctor_set(v___x_1404_, 0, v___x_1406_);
                    v___x_1410_ = v___x_1404_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1408_);
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
    mut v_as_1422_: *mut LeanObject,
    mut v_sz_1423_: *mut LeanObject,
    mut v_i_1424_: *mut LeanObject,
    mut v_b_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1427_: usize = 0;
    let mut v_i_boxed_1428_: usize = 0;
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1423_);
    lean_dec(v_sz_1423_);
    v_i_boxed_1428_ = lean_unbox_usize(v_i_1424_);
    lean_dec(v_i_1424_);
    v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_1422_, v_sz_boxed_1427_, v_i_boxed_1428_, v_b_1425_);
    lean_dec_ref(v_as_1422_);
    return v_res_1429_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(
    mut v_as_1430_: *mut LeanObject,
    mut v_sz_1431_: usize,
    mut v_i_1432_: usize,
    mut v_b_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
    mut v___y_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: usize = 0;
    let mut v___x_1455_: usize = 0;
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_unused_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1443_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
                if v___x_1443_ == 0 {
                    v___x_1444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1444_, 0, v_b_1433_);
                    return v___x_1444_;
                } else {
                    v_snd_1445_ = lean_ctor_get(v_b_1433_, 1);
                    v_isSharedCheck_1463_ = (!lean_is_exclusive(v_b_1433_)) as u8;
                    if v_isSharedCheck_1463_ == 0 {
                        v_unused_1464_ = lean_ctor_get(v_b_1433_, 0);
                        lean_dec(v_unused_1464_);
                        v___x_1447_ = v_b_1433_;
                        v_isShared_1448_ = v_isSharedCheck_1463_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1445_);
                        lean_dec(v_b_1433_);
                        v___x_1447_ = lean_box(0);
                        v_isShared_1448_ = v_isSharedCheck_1463_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1449_ = lean_box(0);
                v_a_1458_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
                if lean_obj_tag(v_a_1458_) == 0 {
                    v_a_1451_ = v_snd_1445_;
                    state = 2;
                    continue;
                } else {
                    v_val_1459_ = lean_ctor_get(v_a_1458_, 0);
                    v___x_1460_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1459_);
                    if v___x_1460_ == 0 {
                        lean_inc(v_val_1459_);
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
                    lean_ctor_set(v___x_1447_, 1, v_a_1451_);
                    lean_ctor_set(v___x_1447_, 0, v___x_1449_);
                    v___x_1453_ = v___x_1447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1449_);
                    lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_a_1451_);
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
    mut v_as_1465_: *mut LeanObject,
    mut v_sz_1466_: *mut LeanObject,
    mut v_i_1467_: *mut LeanObject,
    mut v_b_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1478_: usize = 0;
    let mut v_i_boxed_1479_: usize = 0;
    let mut v_res_1480_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1466_);
    lean_dec(v_sz_1466_);
    v_i_boxed_1479_ = lean_unbox_usize(v_i_1467_);
    lean_dec(v_i_1467_);
    v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_1465_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
    lean_dec(v___y_1476_);
    lean_dec_ref(v___y_1475_);
    lean_dec(v___y_1474_);
    lean_dec_ref(v___y_1473_);
    lean_dec(v___y_1472_);
    lean_dec_ref(v___y_1471_);
    lean_dec(v___y_1470_);
    lean_dec_ref(v___y_1469_);
    lean_dec_ref(v_as_1465_);
    return v_res_1480_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(
    mut v_init_1481_: *mut LeanObject,
    mut v_n_1482_: *mut LeanObject,
    mut v_b_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v_fst_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1513_: u8 = 0;
    let mut v_a_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1521_: u8 = 0;
    let mut v_vs_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1525_: usize = 0;
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1531_: u8 = 0;
    let mut v_fst_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_1482_) == 0 {
                    v_cs_1493_ = lean_ctor_get(v_n_1482_, 0);
                    v___x_1494_ = lean_box(0);
                    v___x_1495_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                    lean_ctor_set(v___x_1495_, 1, v_b_1483_);
                    v_sz_1496_ = lean_array_size(v_cs_1493_);
                    v___x_1497_ = 0usize;
                    v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_1481_, v_cs_1493_, v_sz_1496_, v___x_1497_, v___x_1495_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
                    if lean_obj_tag(v___x_1498_) == 0 {
                        v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1513_ = (!lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1513_ == 0 {
                            v___x_1501_ = v___x_1498_;
                            v_isShared_1502_ = v_isSharedCheck_1513_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1499_);
                            lean_dec(v___x_1498_);
                            v___x_1501_ = lean_box(0);
                            v_isShared_1502_ = v_isSharedCheck_1513_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1514_ = lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1521_ = (!lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1521_ == 0 {
                            v___x_1516_ = v___x_1498_;
                            v_isShared_1517_ = v_isSharedCheck_1521_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1514_);
                            lean_dec(v___x_1498_);
                            v___x_1516_ = lean_box(0);
                            v_isShared_1517_ = v_isSharedCheck_1521_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1522_ = lean_ctor_get(v_n_1482_, 0);
                    v___x_1523_ = lean_box(0);
                    v___x_1524_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1524_, 0, v___x_1523_);
                    lean_ctor_set(v___x_1524_, 1, v_b_1483_);
                    v_sz_1525_ = lean_array_size(v_vs_1522_);
                    v___x_1526_ = 0usize;
                    v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_vs_1522_, v_sz_1525_, v___x_1526_, v___x_1524_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
                    if lean_obj_tag(v___x_1527_) == 0 {
                        v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
                        v_isSharedCheck_1542_ = (!lean_is_exclusive(v___x_1527_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1530_ = v___x_1527_;
                            v_isShared_1531_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1528_);
                            lean_dec(v___x_1527_);
                            v___x_1530_ = lean_box(0);
                            v_isShared_1531_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1543_ = lean_ctor_get(v___x_1527_, 0);
                        v_isSharedCheck_1550_ = (!lean_is_exclusive(v___x_1527_)) as u8;
                        if v_isSharedCheck_1550_ == 0 {
                            v___x_1545_ = v___x_1527_;
                            v_isShared_1546_ = v_isSharedCheck_1550_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1543_);
                            lean_dec(v___x_1527_);
                            v___x_1545_ = lean_box(0);
                            v_isShared_1546_ = v_isSharedCheck_1550_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1503_ = lean_ctor_get(v_a_1499_, 0);
                if lean_obj_tag(v_fst_1503_) == 0 {
                    v_snd_1504_ = lean_ctor_get(v_a_1499_, 1);
                    lean_inc(v_snd_1504_);
                    lean_dec(v_a_1499_);
                    v___x_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1505_, 0, v_snd_1504_);
                    if v_isShared_1502_ == 0 {
                        lean_ctor_set(v___x_1501_, 0, v___x_1505_);
                        v___x_1507_ = v___x_1501_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
                        v___x_1507_ = v_reuseFailAlloc_1508_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1503_);
                    lean_dec(v_a_1499_);
                    v_val_1509_ = lean_ctor_get(v_fst_1503_, 0);
                    lean_inc(v_val_1509_);
                    lean_dec_ref_known(v_fst_1503_, 1);
                    if v_isShared_1502_ == 0 {
                        lean_ctor_set(v___x_1501_, 0, v_val_1509_);
                        v___x_1511_ = v___x_1501_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1509_);
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
                    v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
                    v___x_1519_ = v_reuseFailAlloc_1520_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1519_;
            }
            6 => {
                v_fst_1532_ = lean_ctor_get(v_a_1528_, 0);
                if lean_obj_tag(v_fst_1532_) == 0 {
                    v_snd_1533_ = lean_ctor_get(v_a_1528_, 1);
                    lean_inc(v_snd_1533_);
                    lean_dec(v_a_1528_);
                    v___x_1534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1534_, 0, v_snd_1533_);
                    if v_isShared_1531_ == 0 {
                        lean_ctor_set(v___x_1530_, 0, v___x_1534_);
                        v___x_1536_ = v___x_1530_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
                        v___x_1536_ = v_reuseFailAlloc_1537_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1532_);
                    lean_dec(v_a_1528_);
                    v_val_1538_ = lean_ctor_get(v_fst_1532_, 0);
                    lean_inc(v_val_1538_);
                    lean_dec_ref_known(v_fst_1532_, 1);
                    if v_isShared_1531_ == 0 {
                        lean_ctor_set(v___x_1530_, 0, v_val_1538_);
                        v___x_1540_ = v___x_1530_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_val_1538_);
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
                    v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
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
    mut v_init_1551_: *mut LeanObject,
    mut v_as_1552_: *mut LeanObject,
    mut v_sz_1553_: usize,
    mut v_i_1554_: usize,
    mut v_b_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_a_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: usize = 0;
    let mut v_reuseFailAlloc_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut v_a_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_unused_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1565_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
                if v___x_1565_ == 0 {
                    v___x_1566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1566_, 0, v_b_1555_);
                    return v___x_1566_;
                } else {
                    v_snd_1567_ = lean_ctor_get(v_b_1555_, 1);
                    v_isSharedCheck_1601_ = (!lean_is_exclusive(v_b_1555_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v_unused_1602_ = lean_ctor_get(v_b_1555_, 0);
                        lean_dec(v_unused_1602_);
                        v___x_1569_ = v_b_1555_;
                        v_isShared_1570_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1567_);
                        lean_dec(v_b_1555_);
                        v___x_1569_ = lean_box(0);
                        v_isShared_1570_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1571_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
                lean_inc(v_snd_1567_);
                v___x_1572_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1551_, v_a_1571_, v_snd_1567_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
                if lean_obj_tag(v___x_1572_) == 0 {
                    v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1592_ = (!lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1592_ == 0 {
                        v___x_1575_ = v___x_1572_;
                        v_isShared_1576_ = v_isSharedCheck_1592_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1573_);
                        lean_dec(v___x_1572_);
                        v___x_1575_ = lean_box(0);
                        v_isShared_1576_ = v_isSharedCheck_1592_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1569_);
                    lean_dec(v_snd_1567_);
                    v_a_1593_ = lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1600_ = (!lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1600_ == 0 {
                        v___x_1595_ = v___x_1572_;
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1593_);
                        lean_dec(v___x_1572_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1573_) == 0 {
                    v___x_1577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1577_, 0, v_a_1573_);
                    if v_isShared_1570_ == 0 {
                        lean_ctor_set(v___x_1569_, 0, v___x_1577_);
                        v___x_1579_ = v___x_1569_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
                        lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_snd_1567_);
                        v___x_1579_ = v_reuseFailAlloc_1583_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1575_);
                    lean_dec(v_snd_1567_);
                    v_a_1584_ = lean_ctor_get(v_a_1573_, 0);
                    lean_inc(v_a_1584_);
                    lean_dec_ref_known(v_a_1573_, 1);
                    v___x_1585_ = lean_box(0);
                    if v_isShared_1570_ == 0 {
                        lean_ctor_set(v___x_1569_, 1, v_a_1584_);
                        lean_ctor_set(v___x_1569_, 0, v___x_1585_);
                        v___x_1587_ = v___x_1569_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
                        lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_a_1584_);
                        v___x_1587_ = v_reuseFailAlloc_1591_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1576_ == 0 {
                    lean_ctor_set(v___x_1575_, 0, v___x_1579_);
                    v___x_1581_ = v___x_1575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
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
                    v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
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
    mut v_init_1603_: *mut LeanObject,
    mut v_as_1604_: *mut LeanObject,
    mut v_sz_1605_: *mut LeanObject,
    mut v_i_1606_: *mut LeanObject,
    mut v_b_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1617_: usize = 0;
    let mut v_i_boxed_1618_: usize = 0;
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1617_ = lean_unbox_usize(v_sz_1605_);
    lean_dec(v_sz_1605_);
    v_i_boxed_1618_ = lean_unbox_usize(v_i_1606_);
    lean_dec(v_i_1606_);
    v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_1603_, v_as_1604_, v_sz_boxed_1617_, v_i_boxed_1618_, v_b_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    lean_dec(v___y_1615_);
    lean_dec_ref(v___y_1614_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    lean_dec(v___y_1611_);
    lean_dec_ref(v___y_1610_);
    lean_dec(v___y_1609_);
    lean_dec_ref(v___y_1608_);
    lean_dec_ref(v_as_1604_);
    lean_dec_ref(v_init_1603_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(
    mut v_init_1620_: *mut LeanObject,
    mut v_n_1621_: *mut LeanObject,
    mut v_b_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1632_: *mut LeanObject = core::ptr::null_mut();
    v_res_1632_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1620_, v_n_1621_, v_b_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
    lean_dec(v___y_1630_);
    lean_dec_ref(v___y_1629_);
    lean_dec(v___y_1628_);
    lean_dec_ref(v___y_1627_);
    lean_dec(v___y_1626_);
    lean_dec_ref(v___y_1625_);
    lean_dec(v___y_1624_);
    lean_dec_ref(v___y_1623_);
    lean_dec_ref(v_n_1621_);
    lean_dec_ref(v_init_1620_);
    return v_res_1632_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(
    mut v_as_1633_: *mut LeanObject,
    mut v_sz_1634_: usize,
    mut v_i_1635_: usize,
    mut v_b_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: usize = 0;
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut v_unused_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1638_ = lean_usize_dec_lt(v_i_1635_, v_sz_1634_);
                if v___x_1638_ == 0 {
                    v___x_1639_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1639_, 0, v_b_1636_);
                    return v___x_1639_;
                } else {
                    v_snd_1640_ = lean_ctor_get(v_b_1636_, 1);
                    v_isSharedCheck_1658_ = (!lean_is_exclusive(v_b_1636_)) as u8;
                    if v_isSharedCheck_1658_ == 0 {
                        v_unused_1659_ = lean_ctor_get(v_b_1636_, 0);
                        lean_dec(v_unused_1659_);
                        v___x_1642_ = v_b_1636_;
                        v_isShared_1643_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1640_);
                        lean_dec(v_b_1636_);
                        v___x_1642_ = lean_box(0);
                        v_isShared_1643_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1644_ = lean_box(0);
                v_a_1653_ = lean_array_uget_borrowed(v_as_1633_, v_i_1635_);
                if lean_obj_tag(v_a_1653_) == 0 {
                    v_a_1646_ = v_snd_1640_;
                    state = 2;
                    continue;
                } else {
                    v_val_1654_ = lean_ctor_get(v_a_1653_, 0);
                    v___x_1655_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1654_);
                    if v___x_1655_ == 0 {
                        lean_inc(v_val_1654_);
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
                    lean_ctor_set(v___x_1642_, 1, v_a_1646_);
                    lean_ctor_set(v___x_1642_, 0, v___x_1644_);
                    v___x_1648_ = v___x_1642_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1644_);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1646_);
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
    mut v_as_1660_: *mut LeanObject,
    mut v_sz_1661_: *mut LeanObject,
    mut v_i_1662_: *mut LeanObject,
    mut v_b_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1665_: usize = 0;
    let mut v_i_boxed_1666_: usize = 0;
    let mut v_res_1667_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1665_ = lean_unbox_usize(v_sz_1661_);
    lean_dec(v_sz_1661_);
    v_i_boxed_1666_ = lean_unbox_usize(v_i_1662_);
    lean_dec(v_i_1662_);
    v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_1660_, v_sz_boxed_1665_, v_i_boxed_1666_, v_b_1663_);
    lean_dec_ref(v_as_1660_);
    return v_res_1667_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(
    mut v_as_1668_: *mut LeanObject,
    mut v_sz_1669_: usize,
    mut v_i_1670_: usize,
    mut v_b_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: usize = 0;
    let mut v___x_1693_: usize = 0;
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1681_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
                if v___x_1681_ == 0 {
                    v___x_1682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1682_, 0, v_b_1671_);
                    return v___x_1682_;
                } else {
                    v_snd_1683_ = lean_ctor_get(v_b_1671_, 1);
                    v_isSharedCheck_1701_ = (!lean_is_exclusive(v_b_1671_)) as u8;
                    if v_isSharedCheck_1701_ == 0 {
                        v_unused_1702_ = lean_ctor_get(v_b_1671_, 0);
                        lean_dec(v_unused_1702_);
                        v___x_1685_ = v_b_1671_;
                        v_isShared_1686_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1683_);
                        lean_dec(v_b_1671_);
                        v___x_1685_ = lean_box(0);
                        v_isShared_1686_ = v_isSharedCheck_1701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1687_ = lean_box(0);
                v_a_1696_ = lean_array_uget_borrowed(v_as_1668_, v_i_1670_);
                if lean_obj_tag(v_a_1696_) == 0 {
                    v_a_1689_ = v_snd_1683_;
                    state = 2;
                    continue;
                } else {
                    v_val_1697_ = lean_ctor_get(v_a_1696_, 0);
                    v___x_1698_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1697_);
                    if v___x_1698_ == 0 {
                        lean_inc(v_val_1697_);
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
                    lean_ctor_set(v___x_1685_, 1, v_a_1689_);
                    lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1691_ = v___x_1685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1687_);
                    lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_a_1689_);
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
    mut v_as_1703_: *mut LeanObject,
    mut v_sz_1704_: *mut LeanObject,
    mut v_i_1705_: *mut LeanObject,
    mut v_b_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1716_: usize = 0;
    let mut v_i_boxed_1717_: usize = 0;
    let mut v_res_1718_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1716_ = lean_unbox_usize(v_sz_1704_);
    lean_dec(v_sz_1704_);
    v_i_boxed_1717_ = lean_unbox_usize(v_i_1705_);
    lean_dec(v_i_1705_);
    v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_1703_, v_sz_boxed_1716_, v_i_boxed_1717_, v_b_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    lean_dec(v___y_1714_);
    lean_dec_ref(v___y_1713_);
    lean_dec(v___y_1712_);
    lean_dec_ref(v___y_1711_);
    lean_dec(v___y_1710_);
    lean_dec_ref(v___y_1709_);
    lean_dec(v___y_1708_);
    lean_dec_ref(v___y_1707_);
    lean_dec_ref(v_as_1703_);
    return v_res_1718_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(
    mut v_t_1719_: *mut LeanObject,
    mut v_init_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v_fst_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_a_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_a_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1730_ = lean_ctor_get(v_t_1719_, 0);
                v_tail_1731_ = lean_ctor_get(v_t_1719_, 1);
                lean_inc_ref(v_init_1720_);
                v___x_1732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_1720_, v_root_1730_, v_init_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
                lean_dec_ref(v_init_1720_);
                if lean_obj_tag(v___x_1732_) == 0 {
                    v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
                    v_isSharedCheck_1769_ = (!lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1735_ = v___x_1732_;
                        v_isShared_1736_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1733_);
                        lean_dec(v___x_1732_);
                        v___x_1735_ = lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1770_ = lean_ctor_get(v___x_1732_, 0);
                    v_isSharedCheck_1777_ = (!lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v___x_1772_ = v___x_1732_;
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1770_);
                        lean_dec(v___x_1732_);
                        v___x_1772_ = lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1733_) == 0 {
                    v_a_1737_ = lean_ctor_get(v_a_1733_, 0);
                    lean_inc(v_a_1737_);
                    lean_dec_ref_known(v_a_1733_, 1);
                    if v_isShared_1736_ == 0 {
                        lean_ctor_set(v___x_1735_, 0, v_a_1737_);
                        v___x_1739_ = v___x_1735_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1737_);
                        v___x_1739_ = v_reuseFailAlloc_1740_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1735_);
                    v_a_1741_ = lean_ctor_get(v_a_1733_, 0);
                    lean_inc(v_a_1741_);
                    lean_dec_ref_known(v_a_1733_, 1);
                    v___x_1742_ = lean_box(0);
                    v___x_1743_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    lean_ctor_set(v___x_1743_, 1, v_a_1741_);
                    v_sz_1744_ = lean_array_size(v_tail_1731_);
                    v___x_1745_ = 0usize;
                    v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_tail_1731_, v_sz_1744_, v___x_1745_, v___x_1743_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
                    if lean_obj_tag(v___x_1746_) == 0 {
                        v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1760_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1749_ = v___x_1746_;
                            v_isShared_1750_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1747_);
                            lean_dec(v___x_1746_);
                            v___x_1749_ = lean_box(0);
                            v_isShared_1750_ = v_isSharedCheck_1760_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1761_ = lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1768_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1768_ == 0 {
                            v___x_1763_ = v___x_1746_;
                            v_isShared_1764_ = v_isSharedCheck_1768_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1761_);
                            lean_dec(v___x_1746_);
                            v___x_1763_ = lean_box(0);
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
                v_fst_1751_ = lean_ctor_get(v_a_1747_, 0);
                if lean_obj_tag(v_fst_1751_) == 0 {
                    v_snd_1752_ = lean_ctor_get(v_a_1747_, 1);
                    lean_inc(v_snd_1752_);
                    lean_dec(v_a_1747_);
                    if v_isShared_1750_ == 0 {
                        lean_ctor_set(v___x_1749_, 0, v_snd_1752_);
                        v___x_1754_ = v___x_1749_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_snd_1752_);
                        v___x_1754_ = v_reuseFailAlloc_1755_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1751_);
                    lean_dec(v_a_1747_);
                    v_val_1756_ = lean_ctor_get(v_fst_1751_, 0);
                    lean_inc(v_val_1756_);
                    lean_dec_ref_known(v_fst_1751_, 1);
                    if v_isShared_1750_ == 0 {
                        lean_ctor_set(v___x_1749_, 0, v_val_1756_);
                        v___x_1758_ = v___x_1749_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_val_1756_);
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
                    v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
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
                    v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
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
    mut v_t_1778_: *mut LeanObject,
    mut v_init_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1789_: *mut LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_1778_, v_init_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
    lean_dec(v___y_1787_);
    lean_dec_ref(v___y_1786_);
    lean_dec(v___y_1785_);
    lean_dec_ref(v___y_1784_);
    lean_dec(v___y_1783_);
    lean_dec_ref(v___y_1782_);
    lean_dec(v___y_1781_);
    lean_dec_ref(v___y_1780_);
    lean_dec_ref(v_t_1778_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hs_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_1801_ = lean_ctor_get(v___y_1796_, 2);
    v_decls_1802_ = lean_ctor_get(v_lctx_1801_, 1);
    v_hs_1803_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0;
    v___x_1804_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_decls_1802_, v_hs_1803_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(
    mut v___y_1805_: *mut LeanObject,
    mut v___y_1806_: *mut LeanObject,
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1812_);
    lean_dec_ref(v___y_1811_);
    lean_dec(v___y_1810_);
    lean_dec_ref(v___y_1809_);
    lean_dec(v___y_1808_);
    lean_dec_ref(v___y_1807_);
    lean_dec(v___y_1806_);
    lean_dec_ref(v___y_1805_);
    return v_res_1814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(
    mut v_sz_1815_: usize,
    mut v_i_1816_: usize,
    mut v_bs_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818_: u8 = 0;
    let mut v_v_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1818_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
                if v___x_1818_ == 0 {
                    return v_bs_1817_;
                } else {
                    v_v_1819_ = lean_array_uget(v_bs_1817_, v_i_1816_);
                    v___x_1820_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1821_ = lean_array_uset(v_bs_1817_, v_i_1816_, v___x_1820_);
                    v___x_1822_ = l_Lean_Expr_fvarId_x21(v_v_1819_);
                    lean_dec(v_v_1819_);
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
    mut v_sz_1827_: *mut LeanObject,
    mut v_i_1828_: *mut LeanObject,
    mut v_bs_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1830_: usize = 0;
    let mut v_i_boxed_1831_: usize = 0;
    let mut v_res_1832_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1830_ = lean_unbox_usize(v_sz_1827_);
    lean_dec(v_sz_1827_);
    v_i_boxed_1831_ = lean_unbox_usize(v_i_1828_);
    lean_dec(v_i_1828_);
    v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_boxed_1830_, v_i_boxed_1831_, v_bs_1829_);
    return v_res_1832_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize___lam__2(
    mut v___x_1833_: *mut LeanObject,
    mut v_sz_1834_: usize,
    mut v___x_1835_: usize,
    mut v___x_1836_: *mut LeanObject,
    mut v___x_1837_: *mut LeanObject,
    mut v_stx_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1885_: usize = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut v_hypotheses_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_a_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v___x_1833_, v_sz_1834_, v___x_1835_, v___x_1836_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
                if lean_obj_tag(v___x_1848_) == 0 {
                    v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
                    lean_inc(v_a_1849_);
                    lean_dec_ref_known(v___x_1848_, 1);
                    v_snd_1850_ = lean_ctor_get(v_a_1849_, 1);
                    lean_inc(v_snd_1850_);
                    v_fst_1851_ = lean_ctor_get(v_a_1849_, 0);
                    lean_inc(v_fst_1851_);
                    lean_dec(v_a_1849_);
                    v_fst_1852_ = lean_ctor_get(v_snd_1850_, 0);
                    lean_inc(v_fst_1852_);
                    v_snd_1853_ = lean_ctor_get(v_snd_1850_, 1);
                    lean_inc(v_snd_1853_);
                    lean_dec(v_snd_1850_);
                    v___x_1880_ = lean_unsigned_to_nat(2);
                    v___x_1881_ = l_Lean_Syntax_getArg(v_stx_1838_, v___x_1880_);
                    v___x_1882_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1881_);
                    lean_dec(v___x_1881_);
                    if lean_obj_tag(v___x_1882_) == 0 {
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
                        if lean_obj_tag(v___x_1883_) == 0 {
                            v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                            lean_inc(v_a_1884_);
                            lean_dec_ref_known(v___x_1883_, 1);
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
                            lean_dec(v_snd_1853_);
                            lean_dec(v_fst_1852_);
                            lean_dec(v_fst_1851_);
                            lean_dec(v___x_1837_);
                            v_a_1887_ = lean_ctor_get(v___x_1883_, 0);
                            v_isSharedCheck_1894_ = (!lean_is_exclusive(v___x_1883_)) as u8;
                            if v_isSharedCheck_1894_ == 0 {
                                v___x_1889_ = v___x_1883_;
                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1887_);
                                lean_dec(v___x_1883_);
                                v___x_1889_ = lean_box(0);
                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_hypotheses_1895_ = lean_ctor_get(v___x_1882_, 0);
                        lean_inc_ref(v_hypotheses_1895_);
                        lean_dec_ref_known(v___x_1882_, 1);
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
                        if lean_obj_tag(v___x_1896_) == 0 {
                            v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
                            lean_inc(v_a_1897_);
                            lean_dec_ref_known(v___x_1896_, 1);
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
                            lean_dec(v_snd_1853_);
                            lean_dec(v_fst_1852_);
                            lean_dec(v_fst_1851_);
                            lean_dec(v___x_1837_);
                            v_a_1898_ = lean_ctor_get(v___x_1896_, 0);
                            v_isSharedCheck_1905_ = (!lean_is_exclusive(v___x_1896_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1900_ = v___x_1896_;
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1898_);
                                lean_dec(v___x_1896_);
                                v___x_1900_ = lean_box(0);
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_1837_);
                    v_a_1906_ = lean_ctor_get(v___x_1848_, 0);
                    v_isSharedCheck_1913_ = (!lean_is_exclusive(v___x_1848_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1908_ = v___x_1848_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1906_);
                        lean_dec(v___x_1848_);
                        v___x_1908_ = lean_box(0);
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
                if lean_obj_tag(v___x_1864_) == 0 {
                    v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
                    lean_inc_n(v_a_1865_, 2);
                    lean_dec_ref_known(v___x_1864_, 1);
                    v___x_1866_ = lean_box(0);
                    v___x_1867_ = 3;
                    v___x_1868_ = lean_box((v___x_1867_) as usize);
                    v___x_1869_ = lean_box_usize(v___x_1835_);
                    v___f_1870_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed
                            as *mut core::ffi::c_void,
                        18,
                        9,
                    );
                    lean_closure_set(v___f_1870_, 0, v_a_1865_);
                    lean_closure_set(v___f_1870_, 1, v_snd_1853_);
                    lean_closure_set(v___f_1870_, 2, v_hyps_1855_);
                    lean_closure_set(v___f_1870_, 3, v___x_1866_);
                    lean_closure_set(v___f_1870_, 4, v___x_1868_);
                    lean_closure_set(v___f_1870_, 5, v_fst_1851_);
                    lean_closure_set(v___f_1870_, 6, v_fst_1852_);
                    lean_closure_set(v___f_1870_, 7, v___x_1837_);
                    lean_closure_set(v___f_1870_, 8, v___x_1869_);
                    v___x_1871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_a_1865_, v___f_1870_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
                    return v___x_1871_;
                } else {
                    lean_dec_ref(v_hyps_1855_);
                    lean_dec(v_snd_1853_);
                    lean_dec(v_fst_1852_);
                    lean_dec(v_fst_1851_);
                    lean_dec(v___x_1837_);
                    v_a_1872_ = lean_ctor_get(v___x_1864_, 0);
                    v_isSharedCheck_1879_ = (!lean_is_exclusive(v___x_1864_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1874_ = v___x_1864_;
                        v_isShared_1875_ = v_isSharedCheck_1879_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1872_);
                        lean_dec(v___x_1864_);
                        v___x_1874_ = lean_box(0);
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
                    v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
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
                    v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
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
                    v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
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
                    v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
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
    mut v___x_1914_: *mut LeanObject,
    mut v_sz_1915_: *mut LeanObject,
    mut v___x_1916_: *mut LeanObject,
    mut v___x_1917_: *mut LeanObject,
    mut v___x_1918_: *mut LeanObject,
    mut v_stx_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1929_: usize = 0;
    let mut v___x_10195__boxed_1930_: usize = 0;
    let mut v_res_1931_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1929_ = lean_unbox_usize(v_sz_1915_);
    lean_dec(v_sz_1915_);
    v___x_10195__boxed_1930_ = lean_unbox_usize(v___x_1916_);
    lean_dec(v___x_1916_);
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
    lean_dec(v___y_1927_);
    lean_dec_ref(v___y_1926_);
    lean_dec(v___y_1925_);
    lean_dec_ref(v___y_1924_);
    lean_dec(v___y_1923_);
    lean_dec_ref(v___y_1922_);
    lean_dec(v___y_1921_);
    lean_dec_ref(v___y_1920_);
    lean_dec(v_stx_1919_);
    lean_dec_ref(v___x_1914_);
    return v_res_1931_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalGeneralize(
    mut v_stx_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
    mut v_a_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1956_: usize = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    v___x_1951_ = lean_unsigned_to_nat(0);
    v___x_1952_ = lean_unsigned_to_nat(1);
    v___x_1953_ = l_Lean_Syntax_getArg(v_stx_1941_, v___x_1952_);
    v___x_1954_ = l_Lean_Syntax_getSepArgs(v___x_1953_);
    lean_dec(v___x_1953_);
    v___x_1955_ = l_Lean_Elab_Tactic_evalGeneralize___closed__2;
    v_sz_1956_ = lean_array_size(v___x_1954_);
    v___x_1957_ = lean_box_usize(v_sz_1956_);
    v___x_1958_ = l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1;
    v___f_1959_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    lean_closure_set(v___f_1959_, 0, v___x_1954_);
    lean_closure_set(v___f_1959_, 1, v___x_1957_);
    lean_closure_set(v___f_1959_, 2, v___x_1958_);
    lean_closure_set(v___f_1959_, 3, v___x_1955_);
    lean_closure_set(v___f_1959_, 4, v___x_1951_);
    lean_closure_set(v___f_1959_, 5, v_stx_1941_);
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
    mut v_stx_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1971_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1969_);
    lean_dec_ref(v_a_1968_);
    lean_dec(v_a_1967_);
    lean_dec_ref(v_a_1966_);
    lean_dec(v_a_1965_);
    lean_dec_ref(v_a_1964_);
    lean_dec(v_a_1963_);
    lean_dec_ref(v_a_1962_);
    return v_res_1971_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(
    mut v_as_1972_: *mut LeanObject,
    mut v_sz_1973_: usize,
    mut v_i_1974_: usize,
    mut v_b_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_1972_, v_sz_1973_, v_i_1974_, v_b_1975_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
    return v___x_1985_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(
    mut v_as_1986_: *mut LeanObject,
    mut v_sz_1987_: *mut LeanObject,
    mut v_i_1988_: *mut LeanObject,
    mut v_b_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1999_: usize = 0;
    let mut v_i_boxed_2000_: usize = 0;
    let mut v_res_2001_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1987_);
    lean_dec(v_sz_1987_);
    v_i_boxed_2000_ = lean_unbox_usize(v_i_1988_);
    lean_dec(v_i_1988_);
    v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_1986_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
    lean_dec(v___y_1997_);
    lean_dec_ref(v___y_1996_);
    lean_dec(v___y_1995_);
    lean_dec_ref(v___y_1994_);
    lean_dec(v___y_1993_);
    lean_dec_ref(v___y_1992_);
    lean_dec(v___y_1991_);
    lean_dec_ref(v___y_1990_);
    lean_dec_ref(v_as_1986_);
    return v_res_2001_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(
    mut v_as_2002_: *mut LeanObject,
    mut v_sz_2003_: usize,
    mut v_i_2004_: usize,
    mut v_b_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_2002_, v_sz_2003_, v_i_2004_, v_b_2005_);
    return v___x_2015_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(
    mut v_as_2016_: *mut LeanObject,
    mut v_sz_2017_: *mut LeanObject,
    mut v_i_2018_: *mut LeanObject,
    mut v_b_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2029_: usize = 0;
    let mut v_i_boxed_2030_: usize = 0;
    let mut v_res_2031_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2017_);
    lean_dec(v_sz_2017_);
    v_i_boxed_2030_ = lean_unbox_usize(v_i_2018_);
    lean_dec(v_i_2018_);
    v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_2016_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
    lean_dec(v___y_2027_);
    lean_dec_ref(v___y_2026_);
    lean_dec(v___y_2025_);
    lean_dec_ref(v___y_2024_);
    lean_dec(v___y_2023_);
    lean_dec_ref(v___y_2022_);
    lean_dec(v___y_2021_);
    lean_dec_ref(v___y_2020_);
    lean_dec_ref(v_as_2016_);
    return v_res_2031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(
    mut v_as_2032_: *mut LeanObject,
    mut v_sz_2033_: usize,
    mut v_i_2034_: usize,
    mut v_b_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_2032_, v_sz_2033_, v_i_2034_, v_b_2035_);
    return v___x_2045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(
    mut v_as_2046_: *mut LeanObject,
    mut v_sz_2047_: *mut LeanObject,
    mut v_i_2048_: *mut LeanObject,
    mut v_b_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2059_: usize = 0;
    let mut v_i_boxed_2060_: usize = 0;
    let mut v_res_2061_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2047_);
    lean_dec(v_sz_2047_);
    v_i_boxed_2060_ = lean_unbox_usize(v_i_2048_);
    lean_dec(v_i_2048_);
    v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_2046_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
    lean_dec(v___y_2057_);
    lean_dec_ref(v___y_2056_);
    lean_dec(v___y_2055_);
    lean_dec_ref(v___y_2054_);
    lean_dec(v___y_2053_);
    lean_dec_ref(v___y_2052_);
    lean_dec(v___y_2051_);
    lean_dec_ref(v___y_2050_);
    lean_dec_ref(v_as_2046_);
    return v_res_2061_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1()
-> *mut LeanObject {
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2079_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2080_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4;
    v___x_2081_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7;
    v___x_2082_ = lean_alloc_closure(
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
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2085_: *mut LeanObject = core::ptr::null_mut();
    v_res_2085_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
    return v_res_2085_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3()
-> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7;
    v___x_2113_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6;
    v___x_2114_ = l_Lean_addBuiltinDeclarationRanges(v___x_2112_, v___x_2113_);
    return v___x_2114_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(
    mut v_a_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2116_: *mut LeanObject = core::ptr::null_mut();
    v_res_2116_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
    return v_res_2116_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Generalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Generalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Generalize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Generalize(builtin);
}
