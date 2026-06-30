// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.IndGroupInfo
// Imports: Lean.Meta.InferType
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_pop, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_array_uset, lean_infer_type, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_string_length, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_zip___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_zipWith___at___00List_zip_spec__0;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_reprPrec, lean_name_append_index_after};
use crate::r#gen::Init::Prelude::{
    l_List_lengthTR___redArg, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkBRecOnName;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Declaration::l_Lean_mkRecName;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_instInhabitedExpr, l_Lean_instReprExpr_repr, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_isEquiv, l_Lean_instReprLevel_repr};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isExprDefEqGuarded,
    l_Lean_Meta_mkForallFVars,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_inferArgumentTypesN,
    runtime_initialize_Lean_Meta_InferType,
};
pub static l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instBEqIndGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value:
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
    m_data: [97, 108, 108, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value:
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
    m_data: [110, 117, 109, 78, 101, 115, 116, 101, 100, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instReprIndGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 111, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value:
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
    m_data: [108, 101, 118, 101, 108, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value:
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
    m_data: [112, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instReprIndGroupInst: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_IndGroupInst_toMessageData as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instToMessageDataIndGroupInst: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value: leanh::LeanStringObject<48> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value: leanh::LeanStringObject<52> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 115, 116, 46, 110, 101, 115, 116, 101, 100, 84, 121, 112, 101, 70, 111, 114, 109, 101, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 62, 32, 48, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value:
    leanh::LeanStringObject<60> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 114, 101, 99, 73, 110, 102, 111, 46, 110, 117, 109, 77, 111, 116, 105, 118, 101,
        115, 32, 61, 32, 105, 103, 105, 46, 110, 117, 109, 77, 111, 116, 105, 118, 101, 115, 10,
        32, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
    mut v_xs_1096_: *mut leanh::LeanObject,
    mut v_ys_1097_: *mut leanh::LeanObject,
    mut v_x_1098_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1100_: u8 = 0;
    let mut v_one_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1099_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1100_ = lean_nat_dec_eq(v_x_1098_, v_zero_1099_);
                if v_isZero_1100_ == 1 {
                    leanh::lean_dec(v_x_1098_);
                    return v_isZero_1100_;
                } else {
                    v_one_1101_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1102_ = lean_nat_sub(v_x_1098_, v_one_1101_);
                    leanh::lean_dec(v_x_1098_);
                    v___x_1103_ = lean_array_fget_borrowed(v_xs_1096_, v_n_1102_);
                    v___x_1104_ = lean_array_fget_borrowed(v_ys_1097_, v_n_1102_);
                    v___x_1105_ = lean_name_eq(v___x_1103_, v___x_1104_);
                    if v___x_1105_ == 0 {
                        leanh::lean_dec(v_n_1102_);
                        return v___x_1105_;
                    } else {
                        v_x_1098_ = v_n_1102_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg___boxed(
    mut v_xs_1107_: *mut leanh::LeanObject,
    mut v_ys_1108_: *mut leanh::LeanObject,
    mut v_x_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1110_: u8 = 0;
    let mut v_r_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ =
        l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
            v_xs_1107_, v_ys_1108_, v_x_1109_,
        );
    leanh::lean_dec_ref(v_ys_1108_);
    leanh::lean_dec_ref(v_xs_1107_);
    v_r_1111_ = leanh::lean_box((v_res_1110_) as usize);
    return v_r_1111_;
}
pub unsafe fn l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(
    mut v_x_1112_: *mut leanh::LeanObject,
    mut v_x_1113_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_all_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: u8 = 0;
    v_all_1114_ = leanh::lean_ctor_get(v_x_1112_, 0);
    v_numNested_1115_ = leanh::lean_ctor_get(v_x_1112_, 1);
    v_all_1116_ = leanh::lean_ctor_get(v_x_1113_, 0);
    v_numNested_1117_ = leanh::lean_ctor_get(v_x_1113_, 1);
    v___x_1118_ = lean_array_get_size(v_all_1114_);
    v___x_1119_ = lean_array_get_size(v_all_1116_);
    v___x_1120_ = lean_nat_dec_eq(v___x_1118_, v___x_1119_);
    if v___x_1120_ == 0 {
        return v___x_1120_;
    } else {
        let mut v___x_1121_: u8 = 0;
        v___x_1121_ =
            l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
                v_all_1114_,
                v_all_1116_,
                v___x_1118_,
            );
        if v___x_1121_ == 0 {
            return v___x_1121_;
        } else {
            let mut v___x_1122_: u8 = 0;
            v___x_1122_ = lean_nat_dec_eq(v_numNested_1115_, v_numNested_1117_);
            return v___x_1122_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed(
    mut v_x_1123_: *mut leanh::LeanObject,
    mut v_x_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1125_: u8 = 0;
    let mut v_r_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_x_1123_, v_x_1124_);
    leanh::lean_dec_ref(v_x_1124_);
    leanh::lean_dec_ref(v_x_1123_);
    v_r_1126_ = leanh::lean_box((v_res_1125_) as usize);
    return v_r_1126_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(
    mut v_xs_1127_: *mut leanh::LeanObject,
    mut v_ys_1128_: *mut leanh::LeanObject,
    mut v_hsz_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
    mut v_x_1131_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1132_: u8 = 0;
    v___x_1132_ =
        l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
            v_xs_1127_, v_ys_1128_, v_x_1130_,
        );
    return v___x_1132_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___boxed(
    mut v_xs_1133_: *mut leanh::LeanObject,
    mut v_ys_1134_: *mut leanh::LeanObject,
    mut v_hsz_1135_: *mut leanh::LeanObject,
    mut v_x_1136_: *mut leanh::LeanObject,
    mut v_x_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: u8 = 0;
    let mut v_r_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(
        v_xs_1133_,
        v_ys_1134_,
        v_hsz_1135_,
        v_x_1136_,
        v_x_1137_,
    );
    leanh::lean_dec_ref(v_ys_1134_);
    leanh::lean_dec_ref(v_xs_1133_);
    v_r_1139_ = leanh::lean_box((v_res_1138_) as usize);
    return v_r_1139_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__1(
    mut v_a_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = lean_nat_to_int(v_a_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = leanh::lean_unsigned_to_nat(0);
    v___x_1153_ = l_Lean_Name_reprPrec(v___y_1151_, v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1154_: *mut leanh::LeanObject,
    mut v_x_1155_: *mut leanh::LeanObject,
    mut v_x_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1156_) == 0 {
                    leanh::lean_dec(v_x_1154_);
                    return v_x_1155_;
                } else {
                    v_head_1157_ = leanh::lean_ctor_get(v_x_1156_, 0);
                    v_tail_1158_ = leanh::lean_ctor_get(v_x_1156_, 1);
                    v_isSharedCheck_1169_ = (!leanh::lean_is_exclusive(v_x_1156_)) as u8;
                    if v_isSharedCheck_1169_ == 0 {
                        v___x_1160_ = v_x_1156_;
                        v_isShared_1161_ = v_isSharedCheck_1169_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1158_);
                        leanh::lean_inc(v_head_1157_);
                        leanh::lean_dec(v_x_1156_);
                        v___x_1160_ = leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1169_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1154_);
                if v_isShared_1161_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1160_, 5);
                    leanh::lean_ctor_set(v___x_1160_, 1, v_x_1154_);
                    leanh::lean_ctor_set(v___x_1160_, 0, v_x_1155_);
                    v___x_1163_ = v___x_1160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_x_1155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_x_1154_);
                    v___x_1163_ = v_reuseFailAlloc_1168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1164_ = leanh::lean_unsigned_to_nat(0);
                v___x_1165_ = l_Lean_Name_reprPrec(v_head_1157_, v___x_1164_);
                v___x_1166_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1166_, 0, v___x_1163_);
                leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
                v_x_1155_ = v___x_1166_;
                v_x_1156_ = v_tail_1158_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(
    mut v_x_1170_: *mut leanh::LeanObject,
    mut v_x_1171_: *mut leanh::LeanObject,
    mut v_x_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1172_) == 0 {
                    leanh::lean_dec(v_x_1170_);
                    return v_x_1171_;
                } else {
                    v_head_1173_ = leanh::lean_ctor_get(v_x_1172_, 0);
                    v_tail_1174_ = leanh::lean_ctor_get(v_x_1172_, 1);
                    v_isSharedCheck_1185_ = (!leanh::lean_is_exclusive(v_x_1172_)) as u8;
                    if v_isSharedCheck_1185_ == 0 {
                        v___x_1176_ = v_x_1172_;
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1174_);
                        leanh::lean_inc(v_head_1173_);
                        leanh::lean_dec(v_x_1172_);
                        v___x_1176_ = leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1170_);
                if v_isShared_1177_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1176_, 5);
                    leanh::lean_ctor_set(v___x_1176_, 1, v_x_1170_);
                    leanh::lean_ctor_set(v___x_1176_, 0, v_x_1171_);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_x_1171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_x_1170_);
                    v___x_1179_ = v_reuseFailAlloc_1184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1180_ = leanh::lean_unsigned_to_nat(0);
                v___x_1181_ = l_Lean_Name_reprPrec(v_head_1173_, v___x_1180_);
                v___x_1182_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1182_, 0, v___x_1179_);
                leanh::lean_ctor_set(v___x_1182_, 1, v___x_1181_);
                v___x_1183_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(v_x_1170_, v___x_1182_, v_tail_1174_);
                return v___x_1183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(
    mut v_x_1186_: *mut leanh::LeanObject,
    mut v_x_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1186_) == 0 {
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1187_);
        v___x_1188_ = leanh::lean_box(0);
        return v___x_1188_;
    } else {
        let mut v_tail_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1189_ = leanh::lean_ctor_get(v_x_1186_, 1);
        if leanh::lean_obj_tag(v_tail_1189_) == 0 {
            let mut v_head_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1187_);
            v_head_1190_ = leanh::lean_ctor_get(v_x_1186_, 0);
            leanh::lean_inc(v_head_1190_);
            leanh::lean_dec_ref_known(v_x_1186_, 2);
            v___x_1191_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1190_);
            return v___x_1191_;
        } else {
            let mut v_head_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1189_);
            v_head_1192_ = leanh::lean_ctor_get(v_x_1186_, 0);
            leanh::lean_inc(v_head_1192_);
            leanh::lean_dec_ref_known(v_x_1186_, 2);
            v___x_1193_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1192_);
            v___x_1194_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(v_x_1187_, v___x_1193_, v_tail_1189_);
            return v___x_1194_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0;
    v___x_1204_ = lean_string_length(v___x_1203_);
    return v___x_1204_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5);
    v___x_1206_ = lean_nat_to_int(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(
    mut v_xs_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    v___x_1215_ = lean_array_get_size(v_xs_1214_);
    v___x_1216_ = leanh::lean_unsigned_to_nat(0);
    v___x_1217_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
    if v___x_1217_ == 0 {
        let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1218_ = lean_array_to_list(v_xs_1214_);
        v___x_1219_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1220_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(v___x_1218_, v___x_1219_);
        v___x_1221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
        v___x_1222_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7;
        v___x_1223_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
        leanh::lean_ctor_set(v___x_1223_, 1, v___x_1220_);
        v___x_1224_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1225_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1225_, 0, v___x_1223_);
        leanh::lean_ctor_set(v___x_1225_, 1, v___x_1224_);
        v___x_1226_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1226_, 0, v___x_1221_);
        leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
        v___x_1227_ = l_Std_Format_fill(v___x_1226_);
        return v___x_1227_;
    } else {
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1214_);
        v___x_1228_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10;
        return v___x_1228_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = leanh::lean_unsigned_to_nat(7);
    v___x_1243_ = lean_nat_to_int(v___x_1242_);
    return v___x_1243_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = leanh::lean_unsigned_to_nat(13);
    v___x_1248_ = lean_nat_to_int(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0;
    v___x_1251_ = lean_string_length(v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12,
    );
    v___x_1253_ = lean_nat_to_int(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(
    mut v_x_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_all_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_all_1259_ = leanh::lean_ctor_get(v_x_1258_, 0);
                v_numNested_1260_ = leanh::lean_ctor_get(v_x_1258_, 1);
                v_isSharedCheck_1294_ = (!leanh::lean_is_exclusive(v_x_1258_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1262_ = v_x_1258_;
                    v_isShared_1263_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numNested_1260_);
                    leanh::lean_inc(v_all_1259_);
                    leanh::lean_dec(v_x_1258_);
                    v___x_1262_ = leanh::lean_box(0);
                    v_isShared_1263_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1264_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5;
                v___x_1265_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6;
                v___x_1266_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7,
                );
                v___x_1267_ =
                    l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(
                        v_all_1259_,
                    );
                if v_isShared_1263_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1262_, 4);
                    leanh::lean_ctor_set(v___x_1262_, 1, v___x_1267_);
                    leanh::lean_ctor_set(v___x_1262_, 0, v___x_1266_);
                    v___x_1269_ = v___x_1262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1267_);
                    v___x_1269_ = v_reuseFailAlloc_1293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = 0;
                v___x_1271_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1271_, 0, v___x_1269_);
                leanh::lean_ctor_set_uint8(
                    v___x_1271_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                v___x_1272_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1272_, 0, v___x_1265_);
                leanh::lean_ctor_set(v___x_1272_, 1, v___x_1271_);
                v___x_1273_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2;
                v___x_1274_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1274_, 0, v___x_1272_);
                leanh::lean_ctor_set(v___x_1274_, 1, v___x_1273_);
                v___x_1275_ = leanh::lean_box(1);
                v___x_1276_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1276_, 0, v___x_1274_);
                leanh::lean_ctor_set(v___x_1276_, 1, v___x_1275_);
                v___x_1277_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9;
                v___x_1278_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                leanh::lean_ctor_set(v___x_1278_, 1, v___x_1277_);
                v___x_1279_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1279_, 0, v___x_1278_);
                leanh::lean_ctor_set(v___x_1279_, 1, v___x_1264_);
                v___x_1280_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10,
                );
                v___x_1281_ = l_Nat_reprFast(v_numNested_1260_);
                v___x_1282_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                v___x_1283_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1283_, 0, v___x_1280_);
                leanh::lean_ctor_set(v___x_1283_, 1, v___x_1282_);
                v___x_1284_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
                leanh::lean_ctor_set_uint8(
                    v___x_1284_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                v___x_1285_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1285_, 0, v___x_1279_);
                leanh::lean_ctor_set(v___x_1285_, 1, v___x_1284_);
                v___x_1286_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once
                    ),
                    _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13,
                );
                v___x_1287_ =
                    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14;
                v___x_1288_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1288_, 0, v___x_1287_);
                leanh::lean_ctor_set(v___x_1288_, 1, v___x_1285_);
                v___x_1289_ =
                    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15;
                v___x_1290_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1290_, 0, v___x_1288_);
                leanh::lean_ctor_set(v___x_1290_, 1, v___x_1289_);
                v___x_1291_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1291_, 0, v___x_1286_);
                leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
                v___x_1292_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1292_, 0, v___x_1291_);
                leanh::lean_ctor_set_uint8(
                    v___x_1292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                return v___x_1292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInfo_repr(
    mut v_x_1295_: *mut leanh::LeanObject,
    mut v_prec_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_x_1295_);
    return v___x_1297_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed(
    mut v_x_1298_: *mut leanh::LeanObject,
    mut v_prec_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr(v_x_1298_, v_prec_1299_);
    leanh::lean_dec(v_prec_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(
    mut v_indInfo_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_all_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_all_1304_ = leanh::lean_ctor_get(v_indInfo_1303_, 3);
    leanh::lean_inc(v_all_1304_);
    v_numNested_1305_ = leanh::lean_ctor_get(v_indInfo_1303_, 5);
    leanh::lean_inc(v_numNested_1305_);
    leanh::lean_dec_ref(v_indInfo_1303_);
    v___x_1306_ = lean_array_mk(v_all_1304_);
    v___x_1307_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1307_, 0, v___x_1306_);
    leanh::lean_ctor_set(v___x_1307_, 1, v_numNested_1305_);
    return v___x_1307_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_numMotives(
    mut v_group_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_all_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_all_1309_ = leanh::lean_ctor_get(v_group_1308_, 0);
    v_numNested_1310_ = leanh::lean_ctor_get(v_group_1308_, 1);
    v___x_1311_ = lean_array_get_size(v_all_1309_);
    v___x_1312_ = lean_nat_add(v___x_1311_, v_numNested_1310_);
    return v___x_1312_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_numMotives___boxed(
    mut v_group_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_group_1313_);
    leanh::lean_dec_ref(v_group_1313_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_brecOnName(
    mut v_info_1315_: *mut leanh::LeanObject,
    mut v_idx_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_all_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    v_all_1317_ = leanh::lean_ctor_get(v_info_1315_, 0);
    v___x_1318_ = lean_array_get_size(v_all_1317_);
    v___x_1319_ = lean_nat_dec_lt(v_idx_1316_, v___x_1318_);
    if v___x_1319_ == 0 {
        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_j_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1320_ = lean_nat_sub(v_idx_1316_, v___x_1318_);
        v___x_1321_ = leanh::lean_unsigned_to_nat(1);
        v_j_1322_ = lean_nat_add(v___x_1320_, v___x_1321_);
        leanh::lean_dec(v___x_1320_);
        v___x_1323_ = leanh::lean_unsigned_to_nat(0);
        v___x_1324_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_1315_, v___x_1323_);
        v___x_1325_ = lean_name_append_index_after(v___x_1324_, v_j_1322_);
        return v___x_1325_;
    } else {
        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1326_ = lean_array_fget_borrowed(v_all_1317_, v_idx_1316_);
        leanh::lean_inc(v___x_1326_);
        v___x_1327_ = l_Lean_mkBRecOnName(v___x_1326_);
        return v___x_1327_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_brecOnName___boxed(
    mut v_info_1328_: *mut leanh::LeanObject,
    mut v_idx_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_1328_, v_idx_1329_);
    leanh::lean_dec(v_idx_1329_);
    leanh::lean_dec_ref(v_info_1328_);
    return v_res_1330_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(
    mut v_x_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: *mut leanh::LeanObject,
    mut v_x_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1346_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1341_) == 0 {
                    leanh::lean_dec(v_x_1339_);
                    return v_x_1340_;
                } else {
                    v_head_1342_ = leanh::lean_ctor_get(v_x_1341_, 0);
                    v_tail_1343_ = leanh::lean_ctor_get(v_x_1341_, 1);
                    v_isSharedCheck_1354_ = (!leanh::lean_is_exclusive(v_x_1341_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1345_ = v_x_1341_;
                        v_isShared_1346_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1343_);
                        leanh::lean_inc(v_head_1342_);
                        leanh::lean_dec(v_x_1341_);
                        v___x_1345_ = leanh::lean_box(0);
                        v_isShared_1346_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1339_);
                if v_isShared_1346_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1345_, 5);
                    leanh::lean_ctor_set(v___x_1345_, 1, v_x_1339_);
                    leanh::lean_ctor_set(v___x_1345_, 0, v_x_1340_);
                    v___x_1348_ = v___x_1345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_x_1339_);
                    v___x_1348_ = v_reuseFailAlloc_1353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1349_ = leanh::lean_unsigned_to_nat(0);
                v___x_1350_ = l_Lean_instReprExpr_repr(v_head_1342_, v___x_1349_);
                v___x_1351_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1351_, 0, v___x_1348_);
                leanh::lean_ctor_set(v___x_1351_, 1, v___x_1350_);
                v_x_1340_ = v___x_1351_;
                v_x_1341_ = v_tail_1343_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(
    mut v_x_1355_: *mut leanh::LeanObject,
    mut v_x_1356_: *mut leanh::LeanObject,
    mut v_x_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1357_) == 0 {
                    leanh::lean_dec(v_x_1355_);
                    return v_x_1356_;
                } else {
                    v_head_1358_ = leanh::lean_ctor_get(v_x_1357_, 0);
                    v_tail_1359_ = leanh::lean_ctor_get(v_x_1357_, 1);
                    v_isSharedCheck_1370_ = (!leanh::lean_is_exclusive(v_x_1357_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1361_ = v_x_1357_;
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1359_);
                        leanh::lean_inc(v_head_1358_);
                        leanh::lean_dec(v_x_1357_);
                        v___x_1361_ = leanh::lean_box(0);
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1355_);
                if v_isShared_1362_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1361_, 5);
                    leanh::lean_ctor_set(v___x_1361_, 1, v_x_1355_);
                    leanh::lean_ctor_set(v___x_1361_, 0, v_x_1356_);
                    v___x_1364_ = v___x_1361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_x_1356_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_x_1355_);
                    v___x_1364_ = v_reuseFailAlloc_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1365_ = leanh::lean_unsigned_to_nat(0);
                v___x_1366_ = l_Lean_instReprExpr_repr(v_head_1358_, v___x_1365_);
                v___x_1367_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1367_, 0, v___x_1364_);
                leanh::lean_ctor_set(v___x_1367_, 1, v___x_1366_);
                v___x_1368_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(v_x_1355_, v___x_1367_, v_tail_1359_);
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(
    mut v___y_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = leanh::lean_unsigned_to_nat(0);
    v___x_1373_ = l_Lean_instReprExpr_repr(v___y_1371_, v___x_1372_);
    return v___x_1373_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(
    mut v_x_1374_: *mut leanh::LeanObject,
    mut v_x_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1374_) == 0 {
        let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1375_);
        v___x_1376_ = leanh::lean_box(0);
        return v___x_1376_;
    } else {
        let mut v_tail_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1377_ = leanh::lean_ctor_get(v_x_1374_, 1);
        if leanh::lean_obj_tag(v_tail_1377_) == 0 {
            let mut v_head_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1375_);
            v_head_1378_ = leanh::lean_ctor_get(v_x_1374_, 0);
            leanh::lean_inc(v_head_1378_);
            leanh::lean_dec_ref_known(v_x_1374_, 2);
            v___x_1379_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_1378_);
            return v___x_1379_;
        } else {
            let mut v_head_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1377_);
            v_head_1380_ = leanh::lean_ctor_get(v_x_1374_, 0);
            leanh::lean_inc(v_head_1380_);
            leanh::lean_dec_ref_known(v_x_1374_, 2);
            v___x_1381_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_1380_);
            v___x_1382_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(v_x_1375_, v___x_1381_, v_tail_1377_);
            return v___x_1382_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(
    mut v_xs_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    v___x_1384_ = lean_array_get_size(v_xs_1383_);
    v___x_1385_ = leanh::lean_unsigned_to_nat(0);
    v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
    if v___x_1386_ == 0 {
        let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1387_ = lean_array_to_list(v_xs_1383_);
        v___x_1388_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1389_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(v___x_1387_, v___x_1388_);
        v___x_1390_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
        v___x_1391_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7;
        v___x_1392_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
        leanh::lean_ctor_set(v___x_1392_, 1, v___x_1389_);
        v___x_1393_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1394_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1394_, 0, v___x_1392_);
        leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
        v___x_1395_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1395_, 0, v___x_1390_);
        leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
        v___x_1396_ = l_Std_Format_fill(v___x_1395_);
        return v___x_1396_;
    } else {
        let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1383_);
        v___x_1397_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10;
        return v___x_1397_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v_x_1399_: *mut leanh::LeanObject,
    mut v_x_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1400_) == 0 {
                    leanh::lean_dec(v_x_1398_);
                    return v_x_1399_;
                } else {
                    v_head_1401_ = leanh::lean_ctor_get(v_x_1400_, 0);
                    v_tail_1402_ = leanh::lean_ctor_get(v_x_1400_, 1);
                    v_isSharedCheck_1413_ = (!leanh::lean_is_exclusive(v_x_1400_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1404_ = v_x_1400_;
                        v_isShared_1405_ = v_isSharedCheck_1413_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1402_);
                        leanh::lean_inc(v_head_1401_);
                        leanh::lean_dec(v_x_1400_);
                        v___x_1404_ = leanh::lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1413_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1398_);
                if v_isShared_1405_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1404_, 5);
                    leanh::lean_ctor_set(v___x_1404_, 1, v_x_1398_);
                    leanh::lean_ctor_set(v___x_1404_, 0, v_x_1399_);
                    v___x_1407_ = v___x_1404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_x_1399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1398_);
                    v___x_1407_ = v_reuseFailAlloc_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1408_ = leanh::lean_unsigned_to_nat(0);
                v___x_1409_ = l_Lean_instReprLevel_repr(v_head_1401_, v___x_1408_);
                v___x_1410_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1410_, 0, v___x_1407_);
                leanh::lean_ctor_set(v___x_1410_, 1, v___x_1409_);
                v_x_1399_ = v___x_1410_;
                v_x_1400_ = v_tail_1402_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(
    mut v_x_1414_: *mut leanh::LeanObject,
    mut v_x_1415_: *mut leanh::LeanObject,
    mut v_x_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1421_: u8 = 0;
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1416_) == 0 {
                    leanh::lean_dec(v_x_1414_);
                    return v_x_1415_;
                } else {
                    v_head_1417_ = leanh::lean_ctor_get(v_x_1416_, 0);
                    v_tail_1418_ = leanh::lean_ctor_get(v_x_1416_, 1);
                    v_isSharedCheck_1429_ = (!leanh::lean_is_exclusive(v_x_1416_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v___x_1420_ = v_x_1416_;
                        v_isShared_1421_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1418_);
                        leanh::lean_inc(v_head_1417_);
                        leanh::lean_dec(v_x_1416_);
                        v___x_1420_ = leanh::lean_box(0);
                        v_isShared_1421_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1414_);
                if v_isShared_1421_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1420_, 5);
                    leanh::lean_ctor_set(v___x_1420_, 1, v_x_1414_);
                    leanh::lean_ctor_set(v___x_1420_, 0, v_x_1415_);
                    v___x_1423_ = v___x_1420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_x_1415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_x_1414_);
                    v___x_1423_ = v_reuseFailAlloc_1428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1424_ = leanh::lean_unsigned_to_nat(0);
                v___x_1425_ = l_Lean_instReprLevel_repr(v_head_1417_, v___x_1424_);
                v___x_1426_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1426_, 0, v___x_1423_);
                leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                v___x_1427_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(v_x_1414_, v___x_1426_, v_tail_1418_);
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(
    mut v___y_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = leanh::lean_unsigned_to_nat(0);
    v___x_1432_ = l_Lean_instReprLevel_repr(v___y_1430_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(
    mut v_x_1433_: *mut leanh::LeanObject,
    mut v_x_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1433_) == 0 {
        let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1434_);
        v___x_1435_ = leanh::lean_box(0);
        return v___x_1435_;
    } else {
        let mut v_tail_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1436_ = leanh::lean_ctor_get(v_x_1433_, 1);
        if leanh::lean_obj_tag(v_tail_1436_) == 0 {
            let mut v_head_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1434_);
            v_head_1437_ = leanh::lean_ctor_get(v_x_1433_, 0);
            leanh::lean_inc(v_head_1437_);
            leanh::lean_dec_ref_known(v_x_1433_, 2);
            v___x_1438_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_1437_);
            return v___x_1438_;
        } else {
            let mut v_head_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1436_);
            v_head_1439_ = leanh::lean_ctor_get(v_x_1433_, 0);
            leanh::lean_inc(v_head_1439_);
            leanh::lean_dec_ref_known(v_x_1433_, 2);
            v___x_1440_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_1439_);
            v___x_1441_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(v_x_1434_, v___x_1440_, v_tail_1436_);
            return v___x_1441_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2;
    v___x_1447_ = lean_string_length(v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once), _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3);
    v___x_1449_ = lean_nat_to_int(v___x_1448_);
    return v___x_1449_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(
    mut v_a_1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_1452_) == 0 {
        let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1453_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1;
        return v___x_1453_;
    } else {
        let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: u8 = 0;
        let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1454_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1455_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(v_a_1452_, v___x_1454_);
        v___x_1456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4);
        v___x_1457_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5;
        v___x_1458_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
        leanh::lean_ctor_set(v___x_1458_, 1, v___x_1455_);
        v___x_1459_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1460_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1460_, 0, v___x_1458_);
        leanh::lean_ctor_set(v___x_1460_, 1, v___x_1459_);
        v___x_1461_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1461_, 0, v___x_1456_);
        leanh::lean_ctor_set(v___x_1461_, 1, v___x_1460_);
        v___x_1462_ = 0;
        v___x_1463_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1463_, 0, v___x_1461_);
        leanh::lean_ctor_set_uint8(
            v___x_1463_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1462_,
        );
        return v___x_1463_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = leanh::lean_unsigned_to_nat(18);
    v___x_1474_ = lean_nat_to_int(v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = leanh::lean_unsigned_to_nat(10);
    v___x_1479_ = lean_nat_to_int(v___x_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(
    mut v_x_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toIndGroupInfo_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1484_ = leanh::lean_ctor_get(v_x_1483_, 0);
    leanh::lean_inc_ref(v_toIndGroupInfo_1484_);
    v_levels_1485_ = leanh::lean_ctor_get(v_x_1483_, 1);
    leanh::lean_inc(v_levels_1485_);
    v_params_1486_ = leanh::lean_ctor_get(v_x_1483_, 2);
    leanh::lean_inc_ref(v_params_1486_);
    leanh::lean_dec_ref(v_x_1483_);
    v___x_1487_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5;
    v___x_1488_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3;
    v___x_1489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4,
    );
    v___x_1490_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_toIndGroupInfo_1484_);
    v___x_1491_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1491_, 0, v___x_1489_);
    leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
    v___x_1492_ = 0;
    v___x_1493_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1493_, 0, v___x_1491_);
    leanh::lean_ctor_set_uint8(
        v___x_1493_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1494_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1494_, 0, v___x_1488_);
    leanh::lean_ctor_set(v___x_1494_, 1, v___x_1493_);
    v___x_1495_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2;
    v___x_1496_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1496_, 0, v___x_1494_);
    leanh::lean_ctor_set(v___x_1496_, 1, v___x_1495_);
    v___x_1497_ = leanh::lean_box(1);
    v___x_1498_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1498_, 0, v___x_1496_);
    leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    v___x_1499_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6;
    v___x_1500_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1500_, 0, v___x_1498_);
    leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
    v___x_1501_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
    leanh::lean_ctor_set(v___x_1501_, 1, v___x_1487_);
    v___x_1502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7,
    );
    v___x_1503_ =
        l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(
            v_levels_1485_,
        );
    v___x_1504_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1504_, 0, v___x_1502_);
    leanh::lean_ctor_set(v___x_1504_, 1, v___x_1503_);
    v___x_1505_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    leanh::lean_ctor_set_uint8(
        v___x_1505_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1506_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1506_, 0, v___x_1501_);
    leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
    v___x_1507_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    leanh::lean_ctor_set(v___x_1507_, 1, v___x_1495_);
    v___x_1508_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
    leanh::lean_ctor_set(v___x_1508_, 1, v___x_1497_);
    v___x_1509_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9;
    v___x_1510_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
    leanh::lean_ctor_set(v___x_1510_, 1, v___x_1509_);
    v___x_1511_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
    leanh::lean_ctor_set(v___x_1511_, 1, v___x_1487_);
    v___x_1512_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(
        v_params_1486_,
    );
    v___x_1513_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1502_);
    leanh::lean_ctor_set(v___x_1513_, 1, v___x_1512_);
    v___x_1514_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    leanh::lean_ctor_set_uint8(
        v___x_1514_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1515_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1515_, 0, v___x_1511_);
    leanh::lean_ctor_set(v___x_1515_, 1, v___x_1514_);
    v___x_1516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13,
    );
    v___x_1517_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14;
    v___x_1518_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    leanh::lean_ctor_set(v___x_1518_, 1, v___x_1515_);
    v___x_1519_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15;
    v___x_1520_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1520_, 0, v___x_1518_);
    leanh::lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    v___x_1521_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1521_, 0, v___x_1516_);
    leanh::lean_ctor_set(v___x_1521_, 1, v___x_1520_);
    v___x_1522_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1522_, 0, v___x_1521_);
    leanh::lean_ctor_set_uint8(
        v___x_1522_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    return v___x_1522_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr(
    mut v_x_1523_: *mut leanh::LeanObject,
    mut v_prec_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_x_1523_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(
    mut v_x_1526_: *mut leanh::LeanObject,
    mut v_prec_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr(v_x_1526_, v_prec_1527_);
    leanh::lean_dec(v_prec_1527_);
    return v_res_1528_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(
    mut v_a_1529_: *mut leanh::LeanObject,
    mut v_n_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ =
        l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(
            v_a_1529_,
        );
    return v___x_1531_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_n_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(
        v_a_1532_, v_n_1533_,
    );
    leanh::lean_dec(v_n_1533_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_toMessageData(
    mut v_igi_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toIndGroupInfo_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1538_ = leanh::lean_ctor_get(v_igi_1537_, 0);
    leanh::lean_inc_ref(v_toIndGroupInfo_1538_);
    v_levels_1539_ = leanh::lean_ctor_get(v_igi_1537_, 1);
    leanh::lean_inc(v_levels_1539_);
    v_params_1540_ = leanh::lean_ctor_get(v_igi_1537_, 2);
    leanh::lean_inc_ref(v_params_1540_);
    leanh::lean_dec_ref(v_igi_1537_);
    v_all_1541_ = leanh::lean_ctor_get(v_toIndGroupInfo_1538_, 0);
    leanh::lean_inc_ref(v_all_1541_);
    leanh::lean_dec_ref(v_toIndGroupInfo_1538_);
    v___x_1542_ = leanh::lean_box(0);
    v___x_1543_ = leanh::lean_unsigned_to_nat(0);
    v___x_1544_ = lean_array_get(v___x_1542_, v_all_1541_, v___x_1543_);
    leanh::lean_dec_ref(v_all_1541_);
    v___x_1545_ = l_Lean_Expr_const___override(v___x_1544_, v_levels_1539_);
    v___x_1546_ = l_Lean_mkAppN(v___x_1545_, v_params_1540_);
    leanh::lean_dec_ref(v_params_1540_);
    v___x_1547_ = l_Lean_MessageData_ofExpr(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(
    mut v___x_1550_: u8,
    mut v_____do__lift_1551_: u8,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1551_ == 0 {
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1557_ = leanh::lean_box((v___x_1550_) as usize);
        v___x_1558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1558_, 0, v___x_1557_);
        return v___x_1558_;
    } else {
        let mut v___x_1559_: u8 = 0;
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1559_ = 0;
        v___x_1560_ = leanh::lean_box((v___x_1559_) as usize);
        v___x_1561_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
        return v___x_1561_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(
    mut v___x_1562_: *mut leanh::LeanObject,
    mut v_____do__lift_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
    mut v___y_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
    mut v___y_1568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2319__boxed_1569_: u8 = 0;
    let mut v_____do__lift_2320__boxed_1570_: u8 = 0;
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2319__boxed_1569_ = (leanh::lean_unbox(v___x_1562_) as u8);
    v_____do__lift_2320__boxed_1570_ = (leanh::lean_unbox(v_____do__lift_1563_) as u8);
    v_res_1571_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(
        v___x_2319__boxed_1569_,
        v_____do__lift_2320__boxed_1570_,
        v___y_1564_,
        v___y_1565_,
        v___y_1566_,
        v___y_1567_,
    );
    leanh::lean_dec(v___y_1567_);
    leanh::lean_dec_ref(v___y_1566_);
    leanh::lean_dec(v___y_1565_);
    leanh::lean_dec_ref(v___y_1564_);
    return v_res_1571_;
}
pub unsafe fn l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(
    mut v_x_1572_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1573_: u8 = 0;
    let mut v_head_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1572_) == 0 {
                    v___x_1573_ = 1;
                    return v___x_1573_;
                } else {
                    v_head_1574_ = leanh::lean_ctor_get(v_x_1572_, 0);
                    v_tail_1575_ = leanh::lean_ctor_get(v_x_1572_, 1);
                    v_fst_1576_ = leanh::lean_ctor_get(v_head_1574_, 0);
                    v_snd_1577_ = leanh::lean_ctor_get(v_head_1574_, 1);
                    v___x_1578_ = l_Lean_Level_isEquiv(v_fst_1576_, v_snd_1577_);
                    if v___x_1578_ == 0 {
                        return v___x_1578_;
                    } else {
                        v_x_1572_ = v_tail_1575_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(
    mut v_x_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1581_: u8 = 0;
    let mut v_r_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v_x_1580_);
    leanh::lean_dec(v_x_1580_);
    v_r_1582_ = leanh::lean_box((v_res_1581_) as usize);
    return v_r_1582_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(
    mut v___x_1583_: u8,
    mut v_as_1584_: *mut leanh::LeanObject,
    mut v_i_1585_: usize,
    mut v_stop_1586_: usize,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v_a_1598_: u8 = 0;
    let mut v___x_1599_: usize = 0;
    let mut v___x_1600_: usize = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    let mut v_a_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = lean_usize_dec_eq(v_i_1585_, v_stop_1586_);
                if v___x_1592_ == 0 {
                    v___x_1593_ = lean_array_uget_borrowed(v_as_1584_, v_i_1585_);
                    v_fst_1594_ = leanh::lean_ctor_get(v___x_1593_, 0);
                    v_snd_1595_ = leanh::lean_ctor_get(v___x_1593_, 1);
                    v___x_1596_ = 1;
                    leanh::lean_inc(v_snd_1595_);
                    leanh::lean_inc(v_fst_1594_);
                    v___x_1604_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_fst_1594_,
                        v_snd_1595_,
                        v___y_1587_,
                        v___y_1588_,
                        v___y_1589_,
                        v___y_1590_,
                    );
                    if leanh::lean_obj_tag(v___x_1604_) == 0 {
                        v_a_1605_ = leanh::lean_ctor_get(v___x_1604_, 0);
                        leanh::lean_inc(v_a_1605_);
                        leanh::lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1606_ = (leanh::lean_unbox(v_a_1605_) as u8);
                        leanh::lean_dec(v_a_1605_);
                        if v___x_1606_ == 0 {
                            v_a_1598_ = v___x_1583_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1598_ = v___x_1592_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1604_) == 0 {
                            v_a_1607_ = leanh::lean_ctor_get(v___x_1604_, 0);
                            leanh::lean_inc(v_a_1607_);
                            leanh::lean_dec_ref_known(v___x_1604_, 1);
                            v___x_1608_ = (leanh::lean_unbox(v_a_1607_) as u8);
                            leanh::lean_dec(v_a_1607_);
                            v_a_1598_ = v___x_1608_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_1604_;
                        }
                    }
                } else {
                    v___x_1609_ = 0;
                    v___x_1610_ = leanh::lean_box((v___x_1609_) as usize);
                    v___x_1611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1611_, 0, v___x_1610_);
                    return v___x_1611_;
                }
            }
            1 => {
                if v_a_1598_ == 0 {
                    v___x_1599_ = 1usize;
                    v___x_1600_ = lean_usize_add(v_i_1585_, v___x_1599_);
                    v_i_1585_ = v___x_1600_;
                    state = 0;
                    continue;
                } else {
                    v___x_1602_ = leanh::lean_box((v___x_1596_) as usize);
                    v___x_1603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
                    return v___x_1603_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(
    mut v___x_1612_: *mut leanh::LeanObject,
    mut v_as_1613_: *mut leanh::LeanObject,
    mut v_i_1614_: *mut leanh::LeanObject,
    mut v_stop_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2367__boxed_1621_: u8 = 0;
    let mut v_i_boxed_1622_: usize = 0;
    let mut v_stop_boxed_1623_: usize = 0;
    let mut v_res_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2367__boxed_1621_ = (leanh::lean_unbox(v___x_1612_) as u8);
    v_i_boxed_1622_ = leanh::lean_unbox_usize(v_i_1614_);
    leanh::lean_dec(v_i_1614_);
    v_stop_boxed_1623_ = leanh::lean_unbox_usize(v_stop_1615_);
    leanh::lean_dec(v_stop_1615_);
    v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_2367__boxed_1621_, v_as_1613_, v_i_boxed_1622_, v_stop_boxed_1623_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
    leanh::lean_dec(v___y_1619_);
    leanh::lean_dec_ref(v___y_1618_);
    leanh::lean_dec(v___y_1617_);
    leanh::lean_dec_ref(v___y_1616_);
    leanh::lean_dec_ref(v_as_1613_);
    return v_res_1624_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq(
    mut v_igi1_1625_: *mut leanh::LeanObject,
    mut v_igi2_1626_: *mut leanh::LeanObject,
    mut v_a_1627_: *mut leanh::LeanObject,
    mut v_a_1628_: *mut leanh::LeanObject,
    mut v_a_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toIndGroupInfo_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v_a_1649_: u8 = 0;
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: usize = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toIndGroupInfo_1632_ = leanh::lean_ctor_get(v_igi1_1625_, 0);
                leanh::lean_inc_ref(v_toIndGroupInfo_1632_);
                v_levels_1633_ = leanh::lean_ctor_get(v_igi1_1625_, 1);
                leanh::lean_inc(v_levels_1633_);
                v_params_1634_ = leanh::lean_ctor_get(v_igi1_1625_, 2);
                leanh::lean_inc_ref(v_params_1634_);
                leanh::lean_dec_ref(v_igi1_1625_);
                v_toIndGroupInfo_1635_ = leanh::lean_ctor_get(v_igi2_1626_, 0);
                leanh::lean_inc_ref(v_toIndGroupInfo_1635_);
                v_levels_1636_ = leanh::lean_ctor_get(v_igi2_1626_, 1);
                leanh::lean_inc(v_levels_1636_);
                v_params_1637_ = leanh::lean_ctor_get(v_igi2_1626_, 2);
                leanh::lean_inc_ref(v_params_1637_);
                leanh::lean_dec_ref(v_igi2_1626_);
                v___x_1638_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(
                    v_toIndGroupInfo_1632_,
                    v_toIndGroupInfo_1635_,
                );
                leanh::lean_dec_ref(v_toIndGroupInfo_1635_);
                leanh::lean_dec_ref(v_toIndGroupInfo_1632_);
                if v___x_1638_ == 0 {
                    leanh::lean_dec_ref(v_params_1637_);
                    leanh::lean_dec(v_levels_1636_);
                    leanh::lean_dec_ref(v_params_1634_);
                    leanh::lean_dec(v_levels_1633_);
                    v___x_1639_ = leanh::lean_box((v___x_1638_) as usize);
                    v___x_1640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                    return v___x_1640_;
                } else {
                    v___x_1641_ = l_List_lengthTR___redArg(v_levels_1633_);
                    v___x_1642_ = l_List_lengthTR___redArg(v_levels_1636_);
                    v___x_1643_ = lean_nat_dec_eq(v___x_1641_, v___x_1642_);
                    leanh::lean_dec(v___x_1642_);
                    leanh::lean_dec(v___x_1641_);
                    if v___x_1643_ == 0 {
                        leanh::lean_dec_ref(v_params_1637_);
                        leanh::lean_dec(v_levels_1636_);
                        leanh::lean_dec_ref(v_params_1634_);
                        leanh::lean_dec(v_levels_1633_);
                        v___x_1644_ = leanh::lean_box((v___x_1643_) as usize);
                        v___x_1645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                        return v___x_1645_;
                    } else {
                        v___x_1646_ = l_List_zipWith___at___00List_zip_spec__0(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_levels_1633_,
                            v_levels_1636_,
                        );
                        v___x_1647_ =
                            l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(
                                v___x_1646_,
                            );
                        leanh::lean_dec(v___x_1646_);
                        if v___x_1647_ == 0 {
                            leanh::lean_dec_ref(v_params_1637_);
                            leanh::lean_dec_ref(v_params_1634_);
                            v___x_1658_ = leanh::lean_box((v___x_1647_) as usize);
                            v___x_1659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                            return v___x_1659_;
                        } else {
                            v___x_1660_ = lean_array_get_size(v_params_1634_);
                            v___x_1661_ = lean_array_get_size(v_params_1637_);
                            v___x_1662_ = lean_nat_dec_eq(v___x_1660_, v___x_1661_);
                            if v___x_1662_ == 0 {
                                leanh::lean_dec_ref(v_params_1637_);
                                leanh::lean_dec_ref(v_params_1634_);
                                v___x_1663_ = leanh::lean_box((v___x_1662_) as usize);
                                v___x_1664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
                                return v___x_1664_;
                            } else {
                                v___x_1665_ = l_Array_zip___redArg(v_params_1634_, v_params_1637_);
                                leanh::lean_dec_ref(v_params_1637_);
                                leanh::lean_dec_ref(v_params_1634_);
                                v___x_1666_ = leanh::lean_unsigned_to_nat(0);
                                v___x_1667_ = lean_array_get_size(v___x_1665_);
                                v___x_1668_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
                                if v___x_1668_ == 0 {
                                    leanh::lean_dec_ref(v___x_1665_);
                                    v___x_1669_ =
                                        l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(
                                            v___x_1647_,
                                            v___x_1668_,
                                            v_a_1627_,
                                            v_a_1628_,
                                            v_a_1629_,
                                            v_a_1630_,
                                        );
                                    v___y_1655_ = v___x_1669_;
                                    state = 2;
                                    continue;
                                } else {
                                    if v___x_1668_ == 0 {
                                        leanh::lean_dec_ref(v___x_1665_);
                                        v_a_1649_ = v___x_1647_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1670_ = 0usize;
                                        v___x_1671_ = lean_usize_of_nat(v___x_1667_);
                                        v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_1647_, v___x_1665_, v___x_1670_, v___x_1671_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
                                        leanh::lean_dec_ref(v___x_1665_);
                                        if leanh::lean_obj_tag(v___x_1672_) == 0 {
                                            v_a_1673_ = leanh::lean_ctor_get(v___x_1672_, 0);
                                            leanh::lean_inc(v_a_1673_);
                                            leanh::lean_dec_ref_known(v___x_1672_, 1);
                                            v___x_1674_ =
                                                (leanh::lean_unbox(v_a_1673_) as u8);
                                            leanh::lean_dec(v_a_1673_);
                                            v___x_1675_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v___x_1647_, v___x_1674_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
                                            v___y_1655_ = v___x_1675_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___y_1655_ = v___x_1672_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_a_1649_ == 0 {
                    v___x_1650_ = leanh::lean_box((v_a_1649_) as usize);
                    v___x_1651_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1651_, 0, v___x_1650_);
                    return v___x_1651_;
                } else {
                    v___x_1652_ = leanh::lean_box((v___x_1647_) as usize);
                    v___x_1653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1653_, 0, v___x_1652_);
                    return v___x_1653_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_1655_) == 0 {
                    v_a_1656_ = leanh::lean_ctor_get(v___y_1655_, 0);
                    leanh::lean_inc(v_a_1656_);
                    leanh::lean_dec_ref_known(v___y_1655_, 1);
                    v___x_1657_ = (leanh::lean_unbox(v_a_1656_) as u8);
                    leanh::lean_dec(v_a_1656_);
                    v_a_1649_ = v___x_1657_;
                    state = 1;
                    continue;
                } else {
                    return v___y_1655_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(
    mut v_igi1_1676_: *mut leanh::LeanObject,
    mut v_igi2_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
    mut v_a_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_a_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(
        v_igi1_1676_,
        v_igi2_1677_,
        v_a_1678_,
        v_a_1679_,
        v_a_1680_,
        v_a_1681_,
    );
    leanh::lean_dec(v_a_1681_);
    leanh::lean_dec_ref(v_a_1680_);
    leanh::lean_dec(v_a_1679_);
    leanh::lean_dec_ref(v_a_1678_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_brecOn(
    mut v_group_1684_: *mut leanh::LeanObject,
    mut v_lvl_1685_: *mut leanh::LeanObject,
    mut v_idx_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toIndGroupInfo_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1687_ = leanh::lean_ctor_get(v_group_1684_, 0);
    v_levels_1688_ = leanh::lean_ctor_get(v_group_1684_, 1);
    v_params_1689_ = leanh::lean_ctor_get(v_group_1684_, 2);
    v_n_1690_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_1687_, v_idx_1686_);
    leanh::lean_inc(v_levels_1688_);
    v_us_1691_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v_us_1691_, 0, v_lvl_1685_);
    leanh::lean_ctor_set(v_us_1691_, 1, v_levels_1688_);
    v___x_1692_ = l_Lean_Expr_const___override(v_n_1690_, v_us_1691_);
    v___x_1693_ = l_Lean_mkAppN(v___x_1692_, v_params_1689_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(
    mut v_group_1694_: *mut leanh::LeanObject,
    mut v_lvl_1695_: *mut leanh::LeanObject,
    mut v_idx_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ =
        l_Lean_Elab_Structural_IndGroupInst_brecOn(v_group_1694_, v_lvl_1695_, v_idx_1696_);
    leanh::lean_dec(v_idx_1696_);
    leanh::lean_dec_ref(v_group_1694_);
    return v_res_1697_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
    mut v_msg_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988__overap_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1705_ =
        l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0;
    v___x_988__overap_1706_ = lean_panic_fn_borrowed(v___f_1705_, v_msg_1699_);
    leanh::lean_inc(v___y_1703_);
    leanh::lean_inc_ref(v___y_1702_);
    leanh::lean_inc(v___y_1701_);
    leanh::lean_inc_ref(v___y_1700_);
    v___x_1707_ = leanh::lean_apply_5(
        v___x_988__overap_1706_,
        v___y_1700_,
        v___y_1701_,
        v___y_1702_,
        v___y_1703_,
        leanh::lean_box(0),
    );
    return v___x_1707_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(
    mut v_msg_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
        v_msg_1708_,
        v___y_1709_,
        v___y_1710_,
        v___y_1711_,
        v___y_1712_,
    );
    leanh::lean_dec(v___y_1712_);
    leanh::lean_dec_ref(v___y_1711_);
    leanh::lean_dec(v___y_1710_);
    leanh::lean_dec_ref(v___y_1709_);
    return v_res_1714_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(
    mut v_k_1715_: *mut leanh::LeanObject,
    mut v_b_1716_: *mut leanh::LeanObject,
    mut v_c_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
    mut v___y_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1721_);
    leanh::lean_inc_ref(v___y_1720_);
    leanh::lean_inc(v___y_1719_);
    leanh::lean_inc_ref(v___y_1718_);
    v___x_1723_ = leanh::lean_apply_7(
        v_k_1715_,
        v_b_1716_,
        v_c_1717_,
        v___y_1718_,
        v___y_1719_,
        v___y_1720_,
        v___y_1721_,
        leanh::lean_box(0),
    );
    return v___x_1723_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(
    mut v_k_1724_: *mut leanh::LeanObject,
    mut v_b_1725_: *mut leanh::LeanObject,
    mut v_c_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_1724_, v_b_1725_, v_c_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
    leanh::lean_dec(v___y_1730_);
    leanh::lean_dec_ref(v___y_1729_);
    leanh::lean_dec(v___y_1728_);
    leanh::lean_dec_ref(v___y_1727_);
    return v_res_1732_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(
    mut v_type_1733_: *mut leanh::LeanObject,
    mut v_k_1734_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1735_: u8,
    mut v_whnfType_1736_: u8,
    mut v___y_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_a_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1755_: u8 = 0;
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1742_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1742_, 0, v_k_1734_);
                v___x_1743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_1733_,
                    v___f_1742_,
                    v_cleanupAnnotations_1735_,
                    v_whnfType_1736_,
                    v___y_1737_,
                    v___y_1738_,
                    v___y_1739_,
                    v___y_1740_,
                );
                if leanh::lean_obj_tag(v___x_1743_) == 0 {
                    v_a_1744_ = leanh::lean_ctor_get(v___x_1743_, 0);
                    v_isSharedCheck_1751_ = (!leanh::lean_is_exclusive(v___x_1743_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1746_ = v___x_1743_;
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1744_);
                        leanh::lean_dec(v___x_1743_);
                        v___x_1746_ = leanh::lean_box(0);
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1752_ = leanh::lean_ctor_get(v___x_1743_, 0);
                    v_isSharedCheck_1759_ = (!leanh::lean_is_exclusive(v___x_1743_)) as u8;
                    if v_isSharedCheck_1759_ == 0 {
                        v___x_1754_ = v___x_1743_;
                        v_isShared_1755_ = v_isSharedCheck_1759_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1752_);
                        leanh::lean_dec(v___x_1743_);
                        v___x_1754_ = leanh::lean_box(0);
                        v_isShared_1755_ = v_isSharedCheck_1759_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1747_ == 0 {
                    v___x_1749_ = v___x_1746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
                    v___x_1749_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1749_;
            }
            3 => {
                if v_isShared_1755_ == 0 {
                    v___x_1757_ = v___x_1754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___boxed(
    mut v_type_1760_: *mut leanh::LeanObject,
    mut v_k_1761_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1762_: *mut leanh::LeanObject,
    mut v_whnfType_1763_: *mut leanh::LeanObject,
    mut v___y_1764_: *mut leanh::LeanObject,
    mut v___y_1765_: *mut leanh::LeanObject,
    mut v___y_1766_: *mut leanh::LeanObject,
    mut v___y_1767_: *mut leanh::LeanObject,
    mut v___y_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1769_: u8 = 0;
    let mut v_whnfType_boxed_1770_: u8 = 0;
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1769_ = (leanh::lean_unbox(v_cleanupAnnotations_1762_) as u8);
    v_whnfType_boxed_1770_ = (leanh::lean_unbox(v_whnfType_1763_) as u8);
    v_res_1771_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_1760_, v_k_1761_, v_cleanupAnnotations_boxed_1769_, v_whnfType_boxed_1770_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
    leanh::lean_dec(v___y_1767_);
    leanh::lean_dec_ref(v___y_1766_);
    leanh::lean_dec(v___y_1765_);
    leanh::lean_dec_ref(v___y_1764_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(
    mut v_00_u03b1_1772_: *mut leanh::LeanObject,
    mut v_type_1773_: *mut leanh::LeanObject,
    mut v_k_1774_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1775_: u8,
    mut v_whnfType_1776_: u8,
    mut v___y_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_1773_, v_k_1774_, v_cleanupAnnotations_1775_, v_whnfType_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(
    mut v_00_u03b1_1783_: *mut leanh::LeanObject,
    mut v_type_1784_: *mut leanh::LeanObject,
    mut v_k_1785_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1786_: *mut leanh::LeanObject,
    mut v_whnfType_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
    mut v___y_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1793_: u8 = 0;
    let mut v_whnfType_boxed_1794_: u8 = 0;
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1793_ = (leanh::lean_unbox(v_cleanupAnnotations_1786_) as u8);
    v_whnfType_boxed_1794_ = (leanh::lean_unbox(v_whnfType_1787_) as u8);
    v_res_1795_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(v_00_u03b1_1783_, v_type_1784_, v_k_1785_, v_cleanupAnnotations_boxed_1793_, v_whnfType_boxed_1794_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
    leanh::lean_dec(v___y_1791_);
    leanh::lean_dec_ref(v___y_1790_);
    leanh::lean_dec(v___y_1789_);
    leanh::lean_dec_ref(v___y_1788_);
    return v_res_1795_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(
    mut v_msg_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
    mut v___y_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050__overap_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1802_ =
        l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0;
    v___x_2050__overap_1803_ = lean_panic_fn_borrowed(v___f_1802_, v_msg_1796_);
    leanh::lean_inc(v___y_1800_);
    leanh::lean_inc_ref(v___y_1799_);
    leanh::lean_inc(v___y_1798_);
    leanh::lean_inc_ref(v___y_1797_);
    v___x_1804_ = leanh::lean_apply_5(
        v___x_2050__overap_1803_,
        v___y_1797_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        leanh::lean_box(0),
    );
    return v___x_1804_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(
    mut v_msg_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(
        v_msg_1805_,
        v___y_1806_,
        v___y_1807_,
        v___y_1808_,
        v___y_1809_,
    );
    leanh::lean_dec(v___y_1809_);
    leanh::lean_dec_ref(v___y_1808_);
    leanh::lean_dec(v___y_1807_);
    leanh::lean_dec_ref(v___y_1806_);
    return v_res_1811_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2;
    v___x_1816_ = leanh::lean_unsigned_to_nat(6);
    v___x_1817_ = leanh::lean_unsigned_to_nat(113);
    v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1;
    v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0;
    v___x_1820_ = l_mkPanicMessageWithDecl(
        v___x_1819_,
        v___x_1818_,
        v___x_1817_,
        v___x_1816_,
        v___x_1815_,
    );
    return v___x_1820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(
    mut v___x_1821_: *mut leanh::LeanObject,
    mut v_xs_1822_: *mut leanh::LeanObject,
    mut v_x_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    v___x_1829_ = lean_array_get_size(v_xs_1822_);
    v___x_1830_ = lean_nat_dec_lt(v___x_1821_, v___x_1829_);
    if v___x_1830_ == 0 {
        let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1822_);
        v___x_1831_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3);
        v___x_1832_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
            v___x_1831_,
            v___y_1824_,
            v___y_1825_,
            v___y_1826_,
            v___y_1827_,
        );
        return v___x_1832_;
    } else {
        let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1833_ = l_Lean_instInhabitedExpr;
        v___x_1834_ = leanh::lean_unsigned_to_nat(1);
        v___x_1835_ = lean_nat_sub(v___x_1829_, v___x_1834_);
        v___x_1836_ = lean_array_get_borrowed(v___x_1833_, v_xs_1822_, v___x_1835_);
        leanh::lean_dec(v___x_1835_);
        leanh::lean_inc(v___y_1827_);
        leanh::lean_inc_ref(v___y_1826_);
        leanh::lean_inc(v___y_1825_);
        leanh::lean_inc_ref(v___y_1824_);
        leanh::lean_inc(v___x_1836_);
        v___x_1837_ = lean_infer_type(
            v___x_1836_,
            v___y_1824_,
            v___y_1825_,
            v___y_1826_,
            v___y_1827_,
        );
        if leanh::lean_obj_tag(v___x_1837_) == 0 {
            let mut v_a_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1840_: u8 = 0;
            let mut v___x_1841_: u8 = 0;
            let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1838_ = leanh::lean_ctor_get(v___x_1837_, 0);
            leanh::lean_inc(v_a_1838_);
            leanh::lean_dec_ref_known(v___x_1837_, 1);
            v___x_1839_ = lean_array_pop(v_xs_1822_);
            v___x_1840_ = 0;
            v___x_1841_ = 1;
            v___x_1842_ = l_Lean_Meta_mkForallFVars(
                v___x_1839_,
                v_a_1838_,
                v___x_1840_,
                v___x_1830_,
                v___x_1830_,
                v___x_1841_,
                v___y_1824_,
                v___y_1825_,
                v___y_1826_,
                v___y_1827_,
            );
            leanh::lean_dec_ref(v___x_1839_);
            return v___x_1842_;
        } else {
            leanh::lean_dec_ref(v_xs_1822_);
            return v___x_1837_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(
    mut v___x_1843_: *mut leanh::LeanObject,
    mut v_xs_1844_: *mut leanh::LeanObject,
    mut v_x_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_1843_, v_xs_1844_, v_x_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
    leanh::lean_dec(v___y_1849_);
    leanh::lean_dec_ref(v___y_1848_);
    leanh::lean_dec(v___y_1847_);
    leanh::lean_dec_ref(v___y_1846_);
    leanh::lean_dec_ref(v_x_1845_);
    leanh::lean_dec(v___x_1843_);
    return v_res_1851_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(
    mut v_sz_1854_: usize,
    mut v_i_1855_: usize,
    mut v_bs_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: u8 = 0;
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: usize = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1862_ = lean_usize_dec_lt(v_i_1855_, v_sz_1854_);
                if v___x_1862_ == 0 {
                    v___x_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1863_, 0, v_bs_1856_);
                    return v___x_1863_;
                } else {
                    v___x_1864_ = leanh::lean_unsigned_to_nat(0);
                    v___f_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0;
                    v_v_1866_ = lean_array_uget_borrowed(v_bs_1856_, v_i_1855_);
                    v___x_1867_ = 0;
                    leanh::lean_inc(v_v_1866_);
                    v___x_1868_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_v_1866_, v___f_1865_, v___x_1867_, v___x_1867_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
                    if leanh::lean_obj_tag(v___x_1868_) == 0 {
                        v_a_1869_ = leanh::lean_ctor_get(v___x_1868_, 0);
                        leanh::lean_inc(v_a_1869_);
                        leanh::lean_dec_ref_known(v___x_1868_, 1);
                        v_bs_x27_1870_ = lean_array_uset(v_bs_1856_, v_i_1855_, v___x_1864_);
                        v___x_1871_ = 1usize;
                        v___x_1872_ = lean_usize_add(v_i_1855_, v___x_1871_);
                        v___x_1873_ = lean_array_uset(v_bs_x27_1870_, v_i_1855_, v_a_1869_);
                        v_i_1855_ = v___x_1872_;
                        v_bs_1856_ = v___x_1873_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1856_);
                        v_a_1875_ = leanh::lean_ctor_get(v___x_1868_, 0);
                        v_isSharedCheck_1882_ =
                            (!leanh::lean_is_exclusive(v___x_1868_)) as u8;
                        if v_isSharedCheck_1882_ == 0 {
                            v___x_1877_ = v___x_1868_;
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1875_);
                            leanh::lean_dec(v___x_1868_);
                            v___x_1877_ = leanh::lean_box(0);
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1878_ == 0 {
                    v___x_1880_ = v___x_1877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1881_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
                    v___x_1880_ = v_reuseFailAlloc_1881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(
    mut v_sz_1883_: *mut leanh::LeanObject,
    mut v_i_1884_: *mut leanh::LeanObject,
    mut v_bs_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1891_: usize = 0;
    let mut v_i_boxed_1892_: usize = 0;
    let mut v_res_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1891_ = leanh::lean_unbox_usize(v_sz_1883_);
    leanh::lean_dec(v_sz_1883_);
    v_i_boxed_1892_ = leanh::lean_unbox_usize(v_i_1884_);
    leanh::lean_dec(v_i_1884_);
    v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_sz_boxed_1891_, v_i_boxed_1892_, v_bs_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
    leanh::lean_dec(v___y_1889_);
    leanh::lean_dec_ref(v___y_1888_);
    leanh::lean_dec(v___y_1887_);
    leanh::lean_dec_ref(v___y_1886_);
    return v_res_1893_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1894_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(
    mut v_msg_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v_toFunctor_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___f_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v_toFunctor_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___f_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651__overap_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_unused_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_unused_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_unused_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_unused_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once), _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0);
                v___x_1906_ = l_StateRefT_x27_instMonad___redArg(v___x_1905_);
                v_toApplicative_1907_ = leanh::lean_ctor_get(v___x_1906_, 0);
                v_isSharedCheck_1968_ = (!leanh::lean_is_exclusive(v___x_1906_)) as u8;
                if v_isSharedCheck_1968_ == 0 {
                    v_unused_1969_ = leanh::lean_ctor_get(v___x_1906_, 1);
                    leanh::lean_dec(v_unused_1969_);
                    v___x_1909_ = v___x_1906_;
                    v_isShared_1910_ = v_isSharedCheck_1968_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1907_);
                    leanh::lean_dec(v___x_1906_);
                    v___x_1909_ = leanh::lean_box(0);
                    v_isShared_1910_ = v_isSharedCheck_1968_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1911_ = leanh::lean_ctor_get(v_toApplicative_1907_, 0);
                v_toSeq_1912_ = leanh::lean_ctor_get(v_toApplicative_1907_, 2);
                v_toSeqLeft_1913_ = leanh::lean_ctor_get(v_toApplicative_1907_, 3);
                v_toSeqRight_1914_ = leanh::lean_ctor_get(v_toApplicative_1907_, 4);
                v_isSharedCheck_1966_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1907_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v_unused_1967_ = leanh::lean_ctor_get(v_toApplicative_1907_, 1);
                    leanh::lean_dec(v_unused_1967_);
                    v___x_1916_ = v_toApplicative_1907_;
                    v_isShared_1917_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1914_);
                    leanh::lean_inc(v_toSeqLeft_1913_);
                    leanh::lean_inc(v_toSeq_1912_);
                    leanh::lean_inc(v_toFunctor_1911_);
                    leanh::lean_dec(v_toApplicative_1907_);
                    v___x_1916_ = leanh::lean_box(0);
                    v_isShared_1917_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1918_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1;
                v___f_1919_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1911_);
                v___f_1920_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1920_, 0, v_toFunctor_1911_);
                v___f_1921_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1921_, 0, v_toFunctor_1911_);
                v___x_1922_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1922_, 0, v___f_1920_);
                leanh::lean_ctor_set(v___x_1922_, 1, v___f_1921_);
                v___f_1923_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1923_, 0, v_toSeqRight_1914_);
                v___f_1924_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1924_, 0, v_toSeqLeft_1913_);
                v___f_1925_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1925_, 0, v_toSeq_1912_);
                if v_isShared_1917_ == 0 {
                    leanh::lean_ctor_set(v___x_1916_, 4, v___f_1923_);
                    leanh::lean_ctor_set(v___x_1916_, 3, v___f_1924_);
                    leanh::lean_ctor_set(v___x_1916_, 2, v___f_1925_);
                    leanh::lean_ctor_set(v___x_1916_, 1, v___f_1918_);
                    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1922_);
                    v___x_1927_ = v___x_1916_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___f_1918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 2, v___f_1925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 3, v___f_1924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 4, v___f_1923_);
                    v___x_1927_ = v_reuseFailAlloc_1965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1910_ == 0 {
                    leanh::lean_ctor_set(v___x_1909_, 1, v___f_1919_);
                    leanh::lean_ctor_set(v___x_1909_, 0, v___x_1927_);
                    v___x_1929_ = v___x_1909_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___f_1919_);
                    v___x_1929_ = v_reuseFailAlloc_1964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1930_ = l_StateRefT_x27_instMonad___redArg(v___x_1929_);
                v_toApplicative_1931_ = leanh::lean_ctor_get(v___x_1930_, 0);
                v_isSharedCheck_1962_ = (!leanh::lean_is_exclusive(v___x_1930_)) as u8;
                if v_isSharedCheck_1962_ == 0 {
                    v_unused_1963_ = leanh::lean_ctor_get(v___x_1930_, 1);
                    leanh::lean_dec(v_unused_1963_);
                    v___x_1933_ = v___x_1930_;
                    v_isShared_1934_ = v_isSharedCheck_1962_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1931_);
                    leanh::lean_dec(v___x_1930_);
                    v___x_1933_ = leanh::lean_box(0);
                    v_isShared_1934_ = v_isSharedCheck_1962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1935_ = leanh::lean_ctor_get(v_toApplicative_1931_, 0);
                v_toSeq_1936_ = leanh::lean_ctor_get(v_toApplicative_1931_, 2);
                v_toSeqLeft_1937_ = leanh::lean_ctor_get(v_toApplicative_1931_, 3);
                v_toSeqRight_1938_ = leanh::lean_ctor_get(v_toApplicative_1931_, 4);
                v_isSharedCheck_1960_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1931_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v_unused_1961_ = leanh::lean_ctor_get(v_toApplicative_1931_, 1);
                    leanh::lean_dec(v_unused_1961_);
                    v___x_1940_ = v_toApplicative_1931_;
                    v_isShared_1941_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1938_);
                    leanh::lean_inc(v_toSeqLeft_1937_);
                    leanh::lean_inc(v_toSeq_1936_);
                    leanh::lean_inc(v_toFunctor_1935_);
                    leanh::lean_dec(v_toApplicative_1931_);
                    v___x_1940_ = leanh::lean_box(0);
                    v_isShared_1941_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1942_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3;
                v___f_1943_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4;
                leanh::lean_inc_ref(v_toFunctor_1935_);
                v___f_1944_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1944_, 0, v_toFunctor_1935_);
                v___f_1945_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1945_, 0, v_toFunctor_1935_);
                v___x_1946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1946_, 0, v___f_1944_);
                leanh::lean_ctor_set(v___x_1946_, 1, v___f_1945_);
                v___f_1947_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1947_, 0, v_toSeqRight_1938_);
                v___f_1948_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1948_, 0, v_toSeqLeft_1937_);
                v___f_1949_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1949_, 0, v_toSeq_1936_);
                if v_isShared_1941_ == 0 {
                    leanh::lean_ctor_set(v___x_1940_, 4, v___f_1947_);
                    leanh::lean_ctor_set(v___x_1940_, 3, v___f_1948_);
                    leanh::lean_ctor_set(v___x_1940_, 2, v___f_1949_);
                    leanh::lean_ctor_set(v___x_1940_, 1, v___f_1942_);
                    leanh::lean_ctor_set(v___x_1940_, 0, v___x_1946_);
                    v___x_1951_ = v___x_1940_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___f_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___f_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 3, v___f_1948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___f_1947_);
                    v___x_1951_ = v_reuseFailAlloc_1959_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1934_ == 0 {
                    leanh::lean_ctor_set(v___x_1933_, 1, v___f_1943_);
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1933_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___f_1943_);
                    v___x_1953_ = v_reuseFailAlloc_1958_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1954_ = leanh::lean_box(0);
                v___x_1955_ = l_instInhabitedOfMonad___redArg(v___x_1953_, v___x_1954_);
                v___x_2651__overap_1956_ = lean_panic_fn_borrowed(v___x_1955_, v_msg_1899_);
                leanh::lean_dec(v___x_1955_);
                leanh::lean_inc(v___y_1903_);
                leanh::lean_inc_ref(v___y_1902_);
                leanh::lean_inc(v___y_1901_);
                leanh::lean_inc_ref(v___y_1900_);
                v___x_1957_ = leanh::lean_apply_5(
                    v___x_2651__overap_1956_,
                    v___y_1900_,
                    v___y_1901_,
                    v___y_1902_,
                    v___y_1903_,
                    leanh::lean_box(0),
                );
                return v___x_1957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(
    mut v_msg_1970_: *mut leanh::LeanObject,
    mut v___y_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
    leanh::lean_dec(v___y_1974_);
    leanh::lean_dec_ref(v___y_1973_);
    leanh::lean_dec(v___y_1972_);
    leanh::lean_dec_ref(v___y_1971_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(
    mut v_msgData_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = lean_st_ref_get(v___y_1981_);
    v_env_1984_ = leanh::lean_ctor_get(v___x_1983_, 0);
    leanh::lean_inc_ref(v_env_1984_);
    leanh::lean_dec(v___x_1983_);
    v___x_1985_ = lean_st_ref_get(v___y_1979_);
    v_mctx_1986_ = leanh::lean_ctor_get(v___x_1985_, 0);
    leanh::lean_inc_ref(v_mctx_1986_);
    leanh::lean_dec(v___x_1985_);
    v_lctx_1987_ = leanh::lean_ctor_get(v___y_1978_, 2);
    v_options_1988_ = leanh::lean_ctor_get(v___y_1980_, 2);
    leanh::lean_inc_ref(v_options_1988_);
    leanh::lean_inc_ref(v_lctx_1987_);
    v___x_1989_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1989_, 0, v_env_1984_);
    leanh::lean_ctor_set(v___x_1989_, 1, v_mctx_1986_);
    leanh::lean_ctor_set(v___x_1989_, 2, v_lctx_1987_);
    leanh::lean_ctor_set(v___x_1989_, 3, v_options_1988_);
    v___x_1990_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1989_);
    leanh::lean_ctor_set(v___x_1990_, 1, v_msgData_1977_);
    v___x_1991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1991_, 0, v___x_1990_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(
    mut v_msgData_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
    leanh::lean_dec(v___y_1996_);
    leanh::lean_dec_ref(v___y_1995_);
    leanh::lean_dec(v___y_1994_);
    leanh::lean_dec_ref(v___y_1993_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(
    mut v_msg_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2005_ = leanh::lean_ctor_get(v___y_2002_, 5);
                v___x_2006_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
                v_a_2007_ = leanh::lean_ctor_get(v___x_2006_, 0);
                v_isSharedCheck_2015_ = (!leanh::lean_is_exclusive(v___x_2006_)) as u8;
                if v_isSharedCheck_2015_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2007_);
                    leanh::lean_dec(v___x_2006_);
                    v___x_2009_ = leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2005_);
                v___x_2011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2011_, 0, v_ref_2005_);
                leanh::lean_ctor_set(v___x_2011_, 1, v_a_2007_);
                if v_isShared_2010_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2009_, 1);
                    leanh::lean_ctor_set(v___x_2009_, 0, v___x_2011_);
                    v___x_2013_ = v___x_2009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg___boxed(
    mut v_msg_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    leanh::lean_dec(v___y_2020_);
    leanh::lean_dec_ref(v___y_2019_);
    leanh::lean_dec(v___y_2018_);
    leanh::lean_dec_ref(v___y_2017_);
    return v_res_2022_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0;
    v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2;
    v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6;
    v___x_2033_ = leanh::lean_unsigned_to_nat(11);
    v___x_2034_ = leanh::lean_unsigned_to_nat(129);
    v___x_2035_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5;
    v___x_2036_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4;
    v___x_2037_ = l_mkPanicMessageWithDecl(
        v___x_2036_,
        v___x_2035_,
        v___x_2034_,
        v___x_2033_,
        v___x_2032_,
    );
    return v___x_2037_;
}
pub unsafe fn l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(
    mut v_constName_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2057_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v_val_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_a_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_st_ref_get(v___y_2042_);
                v_env_2053_ = leanh::lean_ctor_get(v___x_2052_, 0);
                leanh::lean_inc_ref(v_env_2053_);
                leanh::lean_dec(v___x_2052_);
                v___x_2054_ = 0;
                leanh::lean_inc(v_constName_2038_);
                v___x_2055_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2053_, v_constName_2038_, v___x_2054_);
                if leanh::lean_obj_tag(v___x_2055_) == 1 {
                    v_val_2056_ = leanh::lean_ctor_get(v___x_2055_, 0);
                    leanh::lean_inc(v_val_2056_);
                    leanh::lean_dec_ref_known(v___x_2055_, 1);
                    v_kind_2057_ = leanh::lean_ctor_get_uint8(
                        v_val_2056_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2057_ == 7 {
                        v___x_2058_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2056_);
                        if leanh::lean_obj_tag(v___x_2058_) == 7 {
                            leanh::lean_dec(v_constName_2038_);
                            v_val_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                            v_isSharedCheck_2066_ =
                                (!leanh::lean_is_exclusive(v___x_2058_)) as u8;
                            if v_isSharedCheck_2066_ == 0 {
                                v___x_2061_ = v___x_2058_;
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2059_);
                                leanh::lean_dec(v___x_2058_);
                                v___x_2061_ = leanh::lean_box(0);
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2058_);
                            v___x_2067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7);
                            v___x_2068_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v___x_2067_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                            if leanh::lean_obj_tag(v___x_2068_) == 0 {
                                v_a_2069_ = leanh::lean_ctor_get(v___x_2068_, 0);
                                v_isSharedCheck_2077_ =
                                    (!leanh::lean_is_exclusive(v___x_2068_)) as u8;
                                if v_isSharedCheck_2077_ == 0 {
                                    v___x_2071_ = v___x_2068_;
                                    v_isShared_2072_ = v_isSharedCheck_2077_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2069_);
                                    leanh::lean_dec(v___x_2068_);
                                    v___x_2071_ = leanh::lean_box(0);
                                    v_isShared_2072_ = v_isSharedCheck_2077_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_2038_);
                                v_a_2078_ = leanh::lean_ctor_get(v___x_2068_, 0);
                                v_isSharedCheck_2085_ =
                                    (!leanh::lean_is_exclusive(v___x_2068_)) as u8;
                                if v_isSharedCheck_2085_ == 0 {
                                    v___x_2080_ = v___x_2068_;
                                    v_isShared_2081_ = v_isSharedCheck_2085_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2078_);
                                    leanh::lean_dec(v___x_2068_);
                                    v___x_2080_ = leanh::lean_box(0);
                                    v_isShared_2081_ = v_isSharedCheck_2085_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_2056_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2055_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2045_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1);
                v___x_2046_ = 0;
                v___x_2047_ = l_Lean_MessageData_ofConstName(v_constName_2038_, v___x_2046_);
                v___x_2048_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2048_, 0, v___x_2045_);
                leanh::lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                v___x_2049_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3);
                v___x_2050_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2050_, 0, v___x_2048_);
                leanh::lean_ctor_set(v___x_2050_, 1, v___x_2049_);
                v___x_2051_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v___x_2050_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                return v___x_2051_;
            }
            2 => {
                if v_isShared_2062_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2061_, 0);
                    v___x_2064_ = v___x_2061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_val_2059_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2064_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_2069_) == 0 {
                    leanh::lean_del_object(v___x_2071_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_2038_);
                    v_val_2073_ = leanh::lean_ctor_get(v_a_2069_, 0);
                    leanh::lean_inc(v_val_2073_);
                    leanh::lean_dec_ref_known(v_a_2069_, 1);
                    if v_isShared_2072_ == 0 {
                        leanh::lean_ctor_set(v___x_2071_, 0, v_val_2073_);
                        v___x_2075_ = v___x_2071_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_val_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2076_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2075_;
            }
            6 => {
                if v_isShared_2081_ == 0 {
                    v___x_2083_ = v___x_2080_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
                    v___x_2083_ = v_reuseFailAlloc_2084_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___boxed(
    mut v_constName_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
    mut v___y_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ =
        l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(
            v_constName_2086_,
            v___y_2087_,
            v___y_2088_,
            v___y_2089_,
            v___y_2090_,
        );
    leanh::lean_dec(v___y_2090_);
    leanh::lean_dec_ref(v___y_2089_);
    leanh::lean_dec(v___y_2088_);
    leanh::lean_dec_ref(v___y_2087_);
    return v_res_2092_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0;
    v___x_2095_ = leanh::lean_unsigned_to_nat(2);
    v___x_2096_ = leanh::lean_unsigned_to_nat(104);
    v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1;
    v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0;
    v___x_2099_ = l_mkPanicMessageWithDecl(
        v___x_2098_,
        v___x_2097_,
        v___x_2096_,
        v___x_2095_,
        v___x_2094_,
    );
    return v___x_2099_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(
    mut v_igi_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
    mut v_a_2104_: *mut leanh::LeanObject,
    mut v_a_2105_: *mut leanh::LeanObject,
    mut v_a_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recName_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_unused_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toIndGroupInfo_2117_ = leanh::lean_ctor_get(v_igi_2102_, 0);
                leanh::lean_inc_ref(v_toIndGroupInfo_2117_);
                v_levels_2118_ = leanh::lean_ctor_get(v_igi_2102_, 1);
                leanh::lean_inc(v_levels_2118_);
                v_params_2119_ = leanh::lean_ctor_get(v_igi_2102_, 2);
                leanh::lean_inc_ref(v_params_2119_);
                leanh::lean_dec_ref(v_igi_2102_);
                v_all_2120_ = leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 0);
                leanh::lean_inc_ref(v_all_2120_);
                v_numNested_2121_ = leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 1);
                v___x_2122_ = leanh::lean_unsigned_to_nat(0);
                v___x_2123_ = lean_nat_dec_eq(v_numNested_2121_, v___x_2122_);
                if v___x_2123_ == 0 {
                    v___x_2124_ = leanh::lean_box(0);
                    v___x_2125_ = lean_array_get_borrowed(v___x_2124_, v_all_2120_, v___x_2122_);
                    leanh::lean_inc(v___x_2125_);
                    v_recName_2126_ = l_Lean_mkRecName(v___x_2125_);
                    leanh::lean_inc(v_recName_2126_);
                    v___x_2127_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_recName_2126_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                    if leanh::lean_obj_tag(v___x_2127_) == 0 {
                        v_a_2128_ = leanh::lean_ctor_get(v___x_2127_, 0);
                        leanh::lean_inc(v_a_2128_);
                        leanh::lean_dec_ref_known(v___x_2127_, 1);
                        v_toConstantVal_2129_ = leanh::lean_ctor_get(v_a_2128_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_2129_);
                        v_numMotives_2130_ = leanh::lean_ctor_get(v_a_2128_, 4);
                        leanh::lean_inc(v_numMotives_2130_);
                        leanh::lean_dec(v_a_2128_);
                        v___x_2140_ =
                            l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_2117_);
                        v_isSharedCheck_2155_ =
                            (!leanh::lean_is_exclusive(v_toIndGroupInfo_2117_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v_unused_2156_ = leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 1);
                            leanh::lean_dec(v_unused_2156_);
                            v_unused_2157_ = leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 0);
                            leanh::lean_dec(v_unused_2157_);
                            v___x_2142_ = v_toIndGroupInfo_2117_;
                            v_isShared_2143_ = v_isSharedCheck_2155_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_toIndGroupInfo_2117_);
                            v___x_2142_ = leanh::lean_box(0);
                            v_isShared_2143_ = v_isSharedCheck_2155_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_recName_2126_);
                        leanh::lean_dec_ref(v_all_2120_);
                        leanh::lean_dec_ref(v_params_2119_);
                        leanh::lean_dec(v_levels_2118_);
                        leanh::lean_dec_ref(v_toIndGroupInfo_2117_);
                        v_a_2158_ = leanh::lean_ctor_get(v___x_2127_, 0);
                        v_isSharedCheck_2165_ =
                            (!leanh::lean_is_exclusive(v___x_2127_)) as u8;
                        if v_isSharedCheck_2165_ == 0 {
                            v___x_2160_ = v___x_2127_;
                            v_isShared_2161_ = v_isSharedCheck_2165_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2158_);
                            leanh::lean_dec(v___x_2127_);
                            v___x_2160_ = leanh::lean_box(0);
                            v_isShared_2161_ = v_isSharedCheck_2165_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_all_2120_);
                    leanh::lean_dec_ref(v_params_2119_);
                    leanh::lean_dec(v_levels_2118_);
                    leanh::lean_dec_ref(v_toIndGroupInfo_2117_);
                    v___x_2166_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2;
                    v___x_2167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2167_, 0, v___x_2166_);
                    return v___x_2167_;
                }
            }
            1 => {
                v___x_2112_ =
                    l_Array_toSubarray___redArg(v___y_2109_, v_lower_2110_, v_upper_2111_);
                v___x_2113_ = l_Subarray_copy___redArg(v___x_2112_);
                v_sz_2114_ = lean_array_size(v___x_2113_);
                v___x_2115_ = 0usize;
                v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_sz_2114_, v___x_2115_, v___x_2113_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                return v___x_2116_;
            }
            2 => {
                v___x_2133_ = l_Lean_Expr_const___override(v_recName_2126_, v___y_2132_);
                v___x_2134_ = l_Lean_mkAppN(v___x_2133_, v_params_2119_);
                leanh::lean_dec_ref(v_params_2119_);
                v___x_2135_ = l_Lean_Meta_inferArgumentTypesN(
                    v_numMotives_2130_,
                    v___x_2134_,
                    v_a_2103_,
                    v_a_2104_,
                    v_a_2105_,
                    v_a_2106_,
                );
                if leanh::lean_obj_tag(v___x_2135_) == 0 {
                    v_a_2136_ = leanh::lean_ctor_get(v___x_2135_, 0);
                    leanh::lean_inc(v_a_2136_);
                    leanh::lean_dec_ref_known(v___x_2135_, 1);
                    v___x_2137_ = lean_array_get_size(v_all_2120_);
                    leanh::lean_dec_ref(v_all_2120_);
                    v___x_2138_ = lean_array_get_size(v_a_2136_);
                    v___x_2139_ = lean_nat_dec_le(v___x_2137_, v___x_2122_);
                    if v___x_2139_ == 0 {
                        v___y_2109_ = v_a_2136_;
                        v_lower_2110_ = v___x_2137_;
                        v_upper_2111_ = v___x_2138_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2109_ = v_a_2136_;
                        v_lower_2110_ = v___x_2122_;
                        v_upper_2111_ = v___x_2138_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_all_2120_);
                    return v___x_2135_;
                }
            }
            3 => {
                v___x_2144_ = lean_nat_dec_eq(v_numMotives_2130_, v___x_2140_);
                leanh::lean_dec(v___x_2140_);
                if v___x_2144_ == 0 {
                    leanh::lean_del_object(v___x_2142_);
                    leanh::lean_dec(v_numMotives_2130_);
                    leanh::lean_dec_ref(v_toConstantVal_2129_);
                    leanh::lean_dec(v_recName_2126_);
                    leanh::lean_dec_ref(v_all_2120_);
                    leanh::lean_dec_ref(v_params_2119_);
                    leanh::lean_dec(v_levels_2118_);
                    v___x_2145_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once
                        ),
                        _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1,
                    );
                    v___x_2146_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v___x_2145_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                    return v___x_2146_;
                } else {
                    v_levelParams_2147_ = leanh::lean_ctor_get(v_toConstantVal_2129_, 1);
                    leanh::lean_inc(v_levelParams_2147_);
                    leanh::lean_dec_ref(v_toConstantVal_2129_);
                    v___x_2148_ = l_List_lengthTR___redArg(v_levels_2118_);
                    v___x_2149_ = l_List_lengthTR___redArg(v_levelParams_2147_);
                    leanh::lean_dec(v_levelParams_2147_);
                    v___x_2150_ = lean_nat_dec_eq(v___x_2148_, v___x_2149_);
                    leanh::lean_dec(v___x_2149_);
                    leanh::lean_dec(v___x_2148_);
                    if v___x_2150_ == 0 {
                        v___x_2151_ = leanh::lean_box(0);
                        if v_isShared_2143_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2142_, 1);
                            leanh::lean_ctor_set(v___x_2142_, 1, v_levels_2118_);
                            leanh::lean_ctor_set(v___x_2142_, 0, v___x_2151_);
                            v___x_2153_ = v___x_2142_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2154_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_levels_2118_);
                            v___x_2153_ = v_reuseFailAlloc_2154_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2142_);
                        v___y_2132_ = v_levels_2118_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___y_2132_ = v___x_2153_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_2161_ == 0 {
                    v___x_2163_ = v___x_2160_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2164_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
                    v___x_2163_ = v_reuseFailAlloc_2164_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___boxed(
    mut v_igi_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
    mut v_a_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(
        v_igi_2168_,
        v_a_2169_,
        v_a_2170_,
        v_a_2171_,
        v_a_2172_,
    );
    leanh::lean_dec(v_a_2172_);
    leanh::lean_dec_ref(v_a_2171_);
    leanh::lean_dec(v_a_2170_);
    leanh::lean_dec_ref(v_a_2169_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(
    mut v_00_u03b1_2175_: *mut leanh::LeanObject,
    mut v_msg_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
    return v___x_2182_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(
    mut v_00_u03b1_2183_: *mut leanh::LeanObject,
    mut v_msg_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(v_00_u03b1_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
    leanh::lean_dec(v___y_2188_);
    leanh::lean_dec_ref(v___y_2187_);
    leanh::lean_dec(v___y_2186_);
    leanh::lean_dec_ref(v___y_2185_);
    return v_res_2190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
}