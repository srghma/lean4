// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.IndGroupInfo
// Imports: Lean.Meta.InferType
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
use crate::ffi::{
    lean_array_pop, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::lean_infer_type;
pub static l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instBEqIndGroupInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value:
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
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value:
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
    m_data: [97, 108, 108, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value:
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
    m_data: [110, 117, 109, 78, 101, 115, 116, 101, 100, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instReprIndGroupInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value:
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
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instInhabitedIndGroupInst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value:
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
        116, 111, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value:
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
    m_data: [108, 101, 118, 101, 108, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value:
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
    m_data: [112, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instReprIndGroupInst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instReprIndGroupInst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_IndGroupInst_toMessageData as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instToMessageDataIndGroupInst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value: crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 73, 110, 100, 71, 114, 111, 117, 112, 73, 110, 115, 116, 46, 110, 101, 115, 116, 101, 100, 84, 121, 112, 101, 70, 111, 114, 109, 101, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 62, 32, 48, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value:
    crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value:
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
static mut l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
    mut v_xs_1096_: *mut crate::leanh::LeanObject,
    mut v_ys_1097_: *mut crate::leanh::LeanObject,
    mut v_x_1098_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1100_: u8 = 0;
    let mut v_one_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1099_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1100_ = lean_nat_dec_eq(v_x_1098_, v_zero_1099_);
                if v_isZero_1100_ == 1 {
                    crate::leanh::lean_dec(v_x_1098_);
                    return v_isZero_1100_;
                } else {
                    v_one_1101_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1102_ = lean_nat_sub(v_x_1098_, v_one_1101_);
                    crate::leanh::lean_dec(v_x_1098_);
                    v___x_1103_ = lean_array_fget_borrowed(v_xs_1096_, v_n_1102_);
                    v___x_1104_ = lean_array_fget_borrowed(v_ys_1097_, v_n_1102_);
                    v___x_1105_ = lean_name_eq(v___x_1103_, v___x_1104_);
                    if v___x_1105_ == 0 {
                        crate::leanh::lean_dec(v_n_1102_);
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
    mut v_xs_1107_: *mut crate::leanh::LeanObject,
    mut v_ys_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1110_: u8 = 0;
    let mut v_r_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ =
        l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
            v_xs_1107_, v_ys_1108_, v_x_1109_,
        );
    crate::leanh::lean_dec_ref(v_ys_1108_);
    crate::leanh::lean_dec_ref(v_xs_1107_);
    v_r_1111_ = crate::leanh::lean_box((v_res_1110_) as usize);
    return v_r_1111_;
}
pub unsafe fn l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(
    mut v_x_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_all_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: u8 = 0;
    v_all_1114_ = crate::leanh::lean_ctor_get(v_x_1112_, 0);
    v_numNested_1115_ = crate::leanh::lean_ctor_get(v_x_1112_, 1);
    v_all_1116_ = crate::leanh::lean_ctor_get(v_x_1113_, 0);
    v_numNested_1117_ = crate::leanh::lean_ctor_get(v_x_1113_, 1);
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
    mut v_x_1123_: *mut crate::leanh::LeanObject,
    mut v_x_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: u8 = 0;
    let mut v_r_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_x_1123_, v_x_1124_);
    crate::leanh::lean_dec_ref(v_x_1124_);
    crate::leanh::lean_dec_ref(v_x_1123_);
    v_r_1126_ = crate::leanh::lean_box((v_res_1125_) as usize);
    return v_r_1126_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(
    mut v_xs_1127_: *mut crate::leanh::LeanObject,
    mut v_ys_1128_: *mut crate::leanh::LeanObject,
    mut v_hsz_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
    mut v_x_1131_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1132_: u8 = 0;
    v___x_1132_ =
        l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(
            v_xs_1127_, v_ys_1128_, v_x_1130_,
        );
    return v___x_1132_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___boxed(
    mut v_xs_1133_: *mut crate::leanh::LeanObject,
    mut v_ys_1134_: *mut crate::leanh::LeanObject,
    mut v_hsz_1135_: *mut crate::leanh::LeanObject,
    mut v_x_1136_: *mut crate::leanh::LeanObject,
    mut v_x_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1138_: u8 = 0;
    let mut v_r_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(
        v_xs_1133_,
        v_ys_1134_,
        v_hsz_1135_,
        v_x_1136_,
        v_x_1137_,
    );
    crate::leanh::lean_dec_ref(v_ys_1134_);
    crate::leanh::lean_dec_ref(v_xs_1133_);
    v_r_1139_ = crate::leanh::lean_box((v_res_1138_) as usize);
    return v_r_1139_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__1(
    mut v_a_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = lean_nat_to_int(v_a_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1153_ = l_Lean_Name_reprPrec(v___y_1151_, v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1154_: *mut crate::leanh::LeanObject,
    mut v_x_1155_: *mut crate::leanh::LeanObject,
    mut v_x_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1156_) == 0 {
                    crate::leanh::lean_dec(v_x_1154_);
                    return v_x_1155_;
                } else {
                    v_head_1157_ = crate::leanh::lean_ctor_get(v_x_1156_, 0);
                    v_tail_1158_ = crate::leanh::lean_ctor_get(v_x_1156_, 1);
                    v_isSharedCheck_1169_ = (!crate::leanh::lean_is_exclusive(v_x_1156_)) as u8;
                    if v_isSharedCheck_1169_ == 0 {
                        v___x_1160_ = v_x_1156_;
                        v_isShared_1161_ = v_isSharedCheck_1169_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1158_);
                        crate::leanh::lean_inc(v_head_1157_);
                        crate::leanh::lean_dec(v_x_1156_);
                        v___x_1160_ = crate::leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1169_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1154_);
                if v_isShared_1161_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1160_, 5);
                    crate::leanh::lean_ctor_set(v___x_1160_, 1, v_x_1154_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 0, v_x_1155_);
                    v___x_1163_ = v___x_1160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_x_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_x_1154_);
                    v___x_1163_ = v_reuseFailAlloc_1168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1164_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1165_ = l_Lean_Name_reprPrec(v_head_1157_, v___x_1164_);
                v___x_1166_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1163_);
                crate::leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
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
    mut v_x_1170_: *mut crate::leanh::LeanObject,
    mut v_x_1171_: *mut crate::leanh::LeanObject,
    mut v_x_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1172_) == 0 {
                    crate::leanh::lean_dec(v_x_1170_);
                    return v_x_1171_;
                } else {
                    v_head_1173_ = crate::leanh::lean_ctor_get(v_x_1172_, 0);
                    v_tail_1174_ = crate::leanh::lean_ctor_get(v_x_1172_, 1);
                    v_isSharedCheck_1185_ = (!crate::leanh::lean_is_exclusive(v_x_1172_)) as u8;
                    if v_isSharedCheck_1185_ == 0 {
                        v___x_1176_ = v_x_1172_;
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1174_);
                        crate::leanh::lean_inc(v_head_1173_);
                        crate::leanh::lean_dec(v_x_1172_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1170_);
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1176_, 5);
                    crate::leanh::lean_ctor_set(v___x_1176_, 1, v_x_1170_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 0, v_x_1171_);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_x_1171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_x_1170_);
                    v___x_1179_ = v_reuseFailAlloc_1184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1180_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1181_ = l_Lean_Name_reprPrec(v_head_1173_, v___x_1180_);
                v___x_1182_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1179_);
                crate::leanh::lean_ctor_set(v___x_1182_, 1, v___x_1181_);
                v___x_1183_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(v_x_1170_, v___x_1182_, v_tail_1174_);
                return v___x_1183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(
    mut v_x_1186_: *mut crate::leanh::LeanObject,
    mut v_x_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1186_) == 0 {
        let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1187_);
        v___x_1188_ = crate::leanh::lean_box(0);
        return v___x_1188_;
    } else {
        let mut v_tail_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1189_ = crate::leanh::lean_ctor_get(v_x_1186_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1189_) == 0 {
            let mut v_head_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1187_);
            v_head_1190_ = crate::leanh::lean_ctor_get(v_x_1186_, 0);
            crate::leanh::lean_inc(v_head_1190_);
            crate::leanh::lean_dec_ref_known(v_x_1186_, 2);
            v___x_1191_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1190_);
            return v___x_1191_;
        } else {
            let mut v_head_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1189_);
            v_head_1192_ = crate::leanh::lean_ctor_get(v_x_1186_, 0);
            crate::leanh::lean_inc(v_head_1192_);
            crate::leanh::lean_dec_ref_known(v_x_1186_, 2);
            v___x_1193_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1192_);
            v___x_1194_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(v_x_1187_, v___x_1193_, v_tail_1189_);
            return v___x_1194_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0;
    v___x_1204_ = lean_string_length(v___x_1203_);
    return v___x_1204_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5);
    v___x_1206_ = lean_nat_to_int(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(
    mut v_xs_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    v___x_1215_ = lean_array_get_size(v_xs_1214_);
    v___x_1216_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1217_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
    if v___x_1217_ == 0 {
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1218_ = lean_array_to_list(v_xs_1214_);
        v___x_1219_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1220_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(v___x_1218_, v___x_1219_);
        v___x_1221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
        v___x_1222_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7;
        v___x_1223_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
        crate::leanh::lean_ctor_set(v___x_1223_, 1, v___x_1220_);
        v___x_1224_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1225_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1225_, 0, v___x_1223_);
        crate::leanh::lean_ctor_set(v___x_1225_, 1, v___x_1224_);
        v___x_1226_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1221_);
        crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
        v___x_1227_ = l_Std_Format_fill(v___x_1226_);
        return v___x_1227_;
    } else {
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1214_);
        v___x_1228_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10;
        return v___x_1228_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_1243_ = lean_nat_to_int(v___x_1242_);
    return v___x_1243_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_1248_ = lean_nat_to_int(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0;
    v___x_1251_ = lean_string_length(v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = crate::leanh::lean_obj_once(
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
    mut v_x_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_all_1259_ = crate::leanh::lean_ctor_get(v_x_1258_, 0);
                v_numNested_1260_ = crate::leanh::lean_ctor_get(v_x_1258_, 1);
                v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v_x_1258_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1262_ = v_x_1258_;
                    v_isShared_1263_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numNested_1260_);
                    crate::leanh::lean_inc(v_all_1259_);
                    crate::leanh::lean_dec(v_x_1258_);
                    v___x_1262_ = crate::leanh::lean_box(0);
                    v_isShared_1263_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1264_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5;
                v___x_1265_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6;
                v___x_1266_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_1262_, 4);
                    crate::leanh::lean_ctor_set(v___x_1262_, 1, v___x_1267_);
                    crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1266_);
                    v___x_1269_ = v___x_1262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1267_);
                    v___x_1269_ = v_reuseFailAlloc_1293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = 0;
                v___x_1271_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1269_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1271_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                v___x_1272_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1272_, 0, v___x_1265_);
                crate::leanh::lean_ctor_set(v___x_1272_, 1, v___x_1271_);
                v___x_1273_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2;
                v___x_1274_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1274_, 0, v___x_1272_);
                crate::leanh::lean_ctor_set(v___x_1274_, 1, v___x_1273_);
                v___x_1275_ = crate::leanh::lean_box(1);
                v___x_1276_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1274_);
                crate::leanh::lean_ctor_set(v___x_1276_, 1, v___x_1275_);
                v___x_1277_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9;
                v___x_1278_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                crate::leanh::lean_ctor_set(v___x_1278_, 1, v___x_1277_);
                v___x_1279_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1279_, 0, v___x_1278_);
                crate::leanh::lean_ctor_set(v___x_1279_, 1, v___x_1264_);
                v___x_1280_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10,
                );
                v___x_1281_ = l_Nat_reprFast(v_numNested_1260_);
                v___x_1282_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                v___x_1283_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1283_, 0, v___x_1280_);
                crate::leanh::lean_ctor_set(v___x_1283_, 1, v___x_1282_);
                v___x_1284_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1284_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                v___x_1285_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1279_);
                crate::leanh::lean_ctor_set(v___x_1285_, 1, v___x_1284_);
                v___x_1286_ = crate::leanh::lean_obj_once(
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
                v___x_1288_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1287_);
                crate::leanh::lean_ctor_set(v___x_1288_, 1, v___x_1285_);
                v___x_1289_ =
                    l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15;
                v___x_1290_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1288_);
                crate::leanh::lean_ctor_set(v___x_1290_, 1, v___x_1289_);
                v___x_1291_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1291_, 0, v___x_1286_);
                crate::leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
                v___x_1292_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1292_, 0, v___x_1291_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1292_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1270_,
                );
                return v___x_1292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInfo_repr(
    mut v_x_1295_: *mut crate::leanh::LeanObject,
    mut v_prec_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_x_1295_);
    return v___x_1297_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed(
    mut v_x_1298_: *mut crate::leanh::LeanObject,
    mut v_prec_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr(v_x_1298_, v_prec_1299_);
    crate::leanh::lean_dec(v_prec_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(
    mut v_indInfo_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_all_1304_ = crate::leanh::lean_ctor_get(v_indInfo_1303_, 3);
    crate::leanh::lean_inc(v_all_1304_);
    v_numNested_1305_ = crate::leanh::lean_ctor_get(v_indInfo_1303_, 5);
    crate::leanh::lean_inc(v_numNested_1305_);
    crate::leanh::lean_dec_ref(v_indInfo_1303_);
    v___x_1306_ = lean_array_mk(v_all_1304_);
    v___x_1307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1307_, 0, v___x_1306_);
    crate::leanh::lean_ctor_set(v___x_1307_, 1, v_numNested_1305_);
    return v___x_1307_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_numMotives(
    mut v_group_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_all_1309_ = crate::leanh::lean_ctor_get(v_group_1308_, 0);
    v_numNested_1310_ = crate::leanh::lean_ctor_get(v_group_1308_, 1);
    v___x_1311_ = lean_array_get_size(v_all_1309_);
    v___x_1312_ = lean_nat_add(v___x_1311_, v_numNested_1310_);
    return v___x_1312_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_numMotives___boxed(
    mut v_group_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_group_1313_);
    crate::leanh::lean_dec_ref(v_group_1313_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_brecOnName(
    mut v_info_1315_: *mut crate::leanh::LeanObject,
    mut v_idx_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    v_all_1317_ = crate::leanh::lean_ctor_get(v_info_1315_, 0);
    v___x_1318_ = lean_array_get_size(v_all_1317_);
    v___x_1319_ = lean_nat_dec_lt(v_idx_1316_, v___x_1318_);
    if v___x_1319_ == 0 {
        let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_j_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1320_ = lean_nat_sub(v_idx_1316_, v___x_1318_);
        v___x_1321_ = crate::leanh::lean_unsigned_to_nat(1);
        v_j_1322_ = lean_nat_add(v___x_1320_, v___x_1321_);
        crate::leanh::lean_dec(v___x_1320_);
        v___x_1323_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1324_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_1315_, v___x_1323_);
        v___x_1325_ = lean_name_append_index_after(v___x_1324_, v_j_1322_);
        return v___x_1325_;
    } else {
        let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1326_ = lean_array_fget_borrowed(v_all_1317_, v_idx_1316_);
        crate::leanh::lean_inc(v___x_1326_);
        v___x_1327_ = l_Lean_mkBRecOnName(v___x_1326_);
        return v___x_1327_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInfo_brecOnName___boxed(
    mut v_info_1328_: *mut crate::leanh::LeanObject,
    mut v_idx_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_1328_, v_idx_1329_);
    crate::leanh::lean_dec(v_idx_1329_);
    crate::leanh::lean_dec_ref(v_info_1328_);
    return v_res_1330_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(
    mut v_x_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
    mut v_x_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1346_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1341_) == 0 {
                    crate::leanh::lean_dec(v_x_1339_);
                    return v_x_1340_;
                } else {
                    v_head_1342_ = crate::leanh::lean_ctor_get(v_x_1341_, 0);
                    v_tail_1343_ = crate::leanh::lean_ctor_get(v_x_1341_, 1);
                    v_isSharedCheck_1354_ = (!crate::leanh::lean_is_exclusive(v_x_1341_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1345_ = v_x_1341_;
                        v_isShared_1346_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1343_);
                        crate::leanh::lean_inc(v_head_1342_);
                        crate::leanh::lean_dec(v_x_1341_);
                        v___x_1345_ = crate::leanh::lean_box(0);
                        v_isShared_1346_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1339_);
                if v_isShared_1346_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1345_, 5);
                    crate::leanh::lean_ctor_set(v___x_1345_, 1, v_x_1339_);
                    crate::leanh::lean_ctor_set(v___x_1345_, 0, v_x_1340_);
                    v___x_1348_ = v___x_1345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_x_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_x_1339_);
                    v___x_1348_ = v_reuseFailAlloc_1353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1349_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1350_ = l_Lean_instReprExpr_repr(v_head_1342_, v___x_1349_);
                v___x_1351_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1348_);
                crate::leanh::lean_ctor_set(v___x_1351_, 1, v___x_1350_);
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
    mut v_x_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
    mut v_x_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1357_) == 0 {
                    crate::leanh::lean_dec(v_x_1355_);
                    return v_x_1356_;
                } else {
                    v_head_1358_ = crate::leanh::lean_ctor_get(v_x_1357_, 0);
                    v_tail_1359_ = crate::leanh::lean_ctor_get(v_x_1357_, 1);
                    v_isSharedCheck_1370_ = (!crate::leanh::lean_is_exclusive(v_x_1357_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1361_ = v_x_1357_;
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1359_);
                        crate::leanh::lean_inc(v_head_1358_);
                        crate::leanh::lean_dec(v_x_1357_);
                        v___x_1361_ = crate::leanh::lean_box(0);
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1355_);
                if v_isShared_1362_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1361_, 5);
                    crate::leanh::lean_ctor_set(v___x_1361_, 1, v_x_1355_);
                    crate::leanh::lean_ctor_set(v___x_1361_, 0, v_x_1356_);
                    v___x_1364_ = v___x_1361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_x_1356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_x_1355_);
                    v___x_1364_ = v_reuseFailAlloc_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1365_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1366_ = l_Lean_instReprExpr_repr(v_head_1358_, v___x_1365_);
                v___x_1367_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1367_, 0, v___x_1364_);
                crate::leanh::lean_ctor_set(v___x_1367_, 1, v___x_1366_);
                v___x_1368_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(v_x_1355_, v___x_1367_, v_tail_1359_);
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1373_ = l_Lean_instReprExpr_repr(v___y_1371_, v___x_1372_);
    return v___x_1373_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(
    mut v_x_1374_: *mut crate::leanh::LeanObject,
    mut v_x_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1374_) == 0 {
        let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1375_);
        v___x_1376_ = crate::leanh::lean_box(0);
        return v___x_1376_;
    } else {
        let mut v_tail_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1377_ = crate::leanh::lean_ctor_get(v_x_1374_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1377_) == 0 {
            let mut v_head_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1375_);
            v_head_1378_ = crate::leanh::lean_ctor_get(v_x_1374_, 0);
            crate::leanh::lean_inc(v_head_1378_);
            crate::leanh::lean_dec_ref_known(v_x_1374_, 2);
            v___x_1379_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_1378_);
            return v___x_1379_;
        } else {
            let mut v_head_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1377_);
            v_head_1380_ = crate::leanh::lean_ctor_get(v_x_1374_, 0);
            crate::leanh::lean_inc(v_head_1380_);
            crate::leanh::lean_dec_ref_known(v_x_1374_, 2);
            v___x_1381_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_1380_);
            v___x_1382_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(v_x_1375_, v___x_1381_, v_tail_1377_);
            return v___x_1382_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(
    mut v_xs_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    v___x_1384_ = lean_array_get_size(v_xs_1383_);
    v___x_1385_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
    if v___x_1386_ == 0 {
        let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1387_ = lean_array_to_list(v_xs_1383_);
        v___x_1388_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1389_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(v___x_1387_, v___x_1388_);
        v___x_1390_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
        v___x_1391_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7;
        v___x_1392_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
        crate::leanh::lean_ctor_set(v___x_1392_, 1, v___x_1389_);
        v___x_1393_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1394_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1394_, 0, v___x_1392_);
        crate::leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
        v___x_1395_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1395_, 0, v___x_1390_);
        crate::leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
        v___x_1396_ = l_Std_Format_fill(v___x_1395_);
        return v___x_1396_;
    } else {
        let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1383_);
        v___x_1397_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10;
        return v___x_1397_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1398_: *mut crate::leanh::LeanObject,
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1400_) == 0 {
                    crate::leanh::lean_dec(v_x_1398_);
                    return v_x_1399_;
                } else {
                    v_head_1401_ = crate::leanh::lean_ctor_get(v_x_1400_, 0);
                    v_tail_1402_ = crate::leanh::lean_ctor_get(v_x_1400_, 1);
                    v_isSharedCheck_1413_ = (!crate::leanh::lean_is_exclusive(v_x_1400_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1404_ = v_x_1400_;
                        v_isShared_1405_ = v_isSharedCheck_1413_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1402_);
                        crate::leanh::lean_inc(v_head_1401_);
                        crate::leanh::lean_dec(v_x_1400_);
                        v___x_1404_ = crate::leanh::lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1413_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1398_);
                if v_isShared_1405_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1404_, 5);
                    crate::leanh::lean_ctor_set(v___x_1404_, 1, v_x_1398_);
                    crate::leanh::lean_ctor_set(v___x_1404_, 0, v_x_1399_);
                    v___x_1407_ = v___x_1404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_x_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1398_);
                    v___x_1407_ = v_reuseFailAlloc_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1408_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1409_ = l_Lean_instReprLevel_repr(v_head_1401_, v___x_1408_);
                v___x_1410_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1407_);
                crate::leanh::lean_ctor_set(v___x_1410_, 1, v___x_1409_);
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
    mut v_x_1414_: *mut crate::leanh::LeanObject,
    mut v_x_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1421_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1416_) == 0 {
                    crate::leanh::lean_dec(v_x_1414_);
                    return v_x_1415_;
                } else {
                    v_head_1417_ = crate::leanh::lean_ctor_get(v_x_1416_, 0);
                    v_tail_1418_ = crate::leanh::lean_ctor_get(v_x_1416_, 1);
                    v_isSharedCheck_1429_ = (!crate::leanh::lean_is_exclusive(v_x_1416_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v___x_1420_ = v_x_1416_;
                        v_isShared_1421_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1418_);
                        crate::leanh::lean_inc(v_head_1417_);
                        crate::leanh::lean_dec(v_x_1416_);
                        v___x_1420_ = crate::leanh::lean_box(0);
                        v_isShared_1421_ = v_isSharedCheck_1429_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1414_);
                if v_isShared_1421_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1420_, 5);
                    crate::leanh::lean_ctor_set(v___x_1420_, 1, v_x_1414_);
                    crate::leanh::lean_ctor_set(v___x_1420_, 0, v_x_1415_);
                    v___x_1423_ = v___x_1420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_x_1415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_x_1414_);
                    v___x_1423_ = v_reuseFailAlloc_1428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1424_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1425_ = l_Lean_instReprLevel_repr(v_head_1417_, v___x_1424_);
                v___x_1426_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1423_);
                crate::leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                v___x_1427_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(v_x_1414_, v___x_1426_, v_tail_1418_);
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(
    mut v___y_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1432_ = l_Lean_instReprLevel_repr(v___y_1430_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(
    mut v_x_1433_: *mut crate::leanh::LeanObject,
    mut v_x_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1433_) == 0 {
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1434_);
        v___x_1435_ = crate::leanh::lean_box(0);
        return v___x_1435_;
    } else {
        let mut v_tail_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1436_ = crate::leanh::lean_ctor_get(v_x_1433_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1436_) == 0 {
            let mut v_head_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1434_);
            v_head_1437_ = crate::leanh::lean_ctor_get(v_x_1433_, 0);
            crate::leanh::lean_inc(v_head_1437_);
            crate::leanh::lean_dec_ref_known(v_x_1433_, 2);
            v___x_1438_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_1437_);
            return v___x_1438_;
        } else {
            let mut v_head_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1436_);
            v_head_1439_ = crate::leanh::lean_ctor_get(v_x_1433_, 0);
            crate::leanh::lean_inc(v_head_1439_);
            crate::leanh::lean_dec_ref_known(v_x_1433_, 2);
            v___x_1440_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_1439_);
            v___x_1441_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(v_x_1434_, v___x_1440_, v_tail_1436_);
            return v___x_1441_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2;
    v___x_1447_ = lean_string_length(v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once), _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3);
    v___x_1449_ = lean_nat_to_int(v___x_1448_);
    return v___x_1449_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(
    mut v_a_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_1452_) == 0 {
        let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1453_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1;
        return v___x_1453_;
    } else {
        let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: u8 = 0;
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1454_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3;
        v___x_1455_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(v_a_1452_, v___x_1454_);
        v___x_1456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4);
        v___x_1457_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5;
        v___x_1458_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
        crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1455_);
        v___x_1459_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8;
        v___x_1460_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1458_);
        crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1459_);
        v___x_1461_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1456_);
        crate::leanh::lean_ctor_set(v___x_1461_, 1, v___x_1460_);
        v___x_1462_ = 0;
        v___x_1463_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1461_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1463_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1462_,
        );
        return v___x_1463_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_1474_ = lean_nat_to_int(v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1479_ = lean_nat_to_int(v___x_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(
    mut v_x_1483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toIndGroupInfo_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1484_ = crate::leanh::lean_ctor_get(v_x_1483_, 0);
    crate::leanh::lean_inc_ref(v_toIndGroupInfo_1484_);
    v_levels_1485_ = crate::leanh::lean_ctor_get(v_x_1483_, 1);
    crate::leanh::lean_inc(v_levels_1485_);
    v_params_1486_ = crate::leanh::lean_ctor_get(v_x_1483_, 2);
    crate::leanh::lean_inc_ref(v_params_1486_);
    crate::leanh::lean_dec_ref(v_x_1483_);
    v___x_1487_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5;
    v___x_1488_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3;
    v___x_1489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4,
    );
    v___x_1490_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_toIndGroupInfo_1484_);
    v___x_1491_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1491_, 0, v___x_1489_);
    crate::leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
    v___x_1492_ = 0;
    v___x_1493_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1493_, 0, v___x_1491_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1493_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1494_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1494_, 1, v___x_1493_);
    v___x_1495_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2;
    v___x_1496_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1494_);
    crate::leanh::lean_ctor_set(v___x_1496_, 1, v___x_1495_);
    v___x_1497_ = crate::leanh::lean_box(1);
    v___x_1498_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1496_);
    crate::leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    v___x_1499_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6;
    v___x_1500_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1498_);
    crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
    v___x_1501_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
    crate::leanh::lean_ctor_set(v___x_1501_, 1, v___x_1487_);
    v___x_1502_ = crate::leanh::lean_obj_once(
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
    v___x_1504_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1504_, 0, v___x_1502_);
    crate::leanh::lean_ctor_set(v___x_1504_, 1, v___x_1503_);
    v___x_1505_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1505_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1506_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1506_, 0, v___x_1501_);
    crate::leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
    v___x_1507_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1495_);
    v___x_1508_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1497_);
    v___x_1509_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9;
    v___x_1510_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
    crate::leanh::lean_ctor_set(v___x_1510_, 1, v___x_1509_);
    v___x_1511_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
    crate::leanh::lean_ctor_set(v___x_1511_, 1, v___x_1487_);
    v___x_1512_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(
        v_params_1486_,
    );
    v___x_1513_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1502_);
    crate::leanh::lean_ctor_set(v___x_1513_, 1, v___x_1512_);
    v___x_1514_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1514_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    v___x_1515_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1515_, 0, v___x_1511_);
    crate::leanh::lean_ctor_set(v___x_1515_, 1, v___x_1514_);
    v___x_1516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13,
    );
    v___x_1517_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14;
    v___x_1518_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1515_);
    v___x_1519_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15;
    v___x_1520_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1518_);
    crate::leanh::lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    v___x_1521_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1521_, 0, v___x_1516_);
    crate::leanh::lean_ctor_set(v___x_1521_, 1, v___x_1520_);
    v___x_1522_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1522_, 0, v___x_1521_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1522_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1492_,
    );
    return v___x_1522_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr(
    mut v_x_1523_: *mut crate::leanh::LeanObject,
    mut v_prec_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_x_1523_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(
    mut v_x_1526_: *mut crate::leanh::LeanObject,
    mut v_prec_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr(v_x_1526_, v_prec_1527_);
    crate::leanh::lean_dec(v_prec_1527_);
    return v_res_1528_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(
    mut v_a_1529_: *mut crate::leanh::LeanObject,
    mut v_n_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ =
        l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(
            v_a_1529_,
        );
    return v___x_1531_;
}
pub unsafe fn l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_n_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(
        v_a_1532_, v_n_1533_,
    );
    crate::leanh::lean_dec(v_n_1533_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_toMessageData(
    mut v_igi_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toIndGroupInfo_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1538_ = crate::leanh::lean_ctor_get(v_igi_1537_, 0);
    crate::leanh::lean_inc_ref(v_toIndGroupInfo_1538_);
    v_levels_1539_ = crate::leanh::lean_ctor_get(v_igi_1537_, 1);
    crate::leanh::lean_inc(v_levels_1539_);
    v_params_1540_ = crate::leanh::lean_ctor_get(v_igi_1537_, 2);
    crate::leanh::lean_inc_ref(v_params_1540_);
    crate::leanh::lean_dec_ref(v_igi_1537_);
    v_all_1541_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_1538_, 0);
    crate::leanh::lean_inc_ref(v_all_1541_);
    crate::leanh::lean_dec_ref(v_toIndGroupInfo_1538_);
    v___x_1542_ = crate::leanh::lean_box(0);
    v___x_1543_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1544_ = lean_array_get(v___x_1542_, v_all_1541_, v___x_1543_);
    crate::leanh::lean_dec_ref(v_all_1541_);
    v___x_1545_ = l_Lean_Expr_const___override(v___x_1544_, v_levels_1539_);
    v___x_1546_ = l_Lean_mkAppN(v___x_1545_, v_params_1540_);
    crate::leanh::lean_dec_ref(v_params_1540_);
    v___x_1547_ = l_Lean_MessageData_ofExpr(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(
    mut v___x_1550_: u8,
    mut v_____do__lift_1551_: u8,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1551_ == 0 {
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1557_ = crate::leanh::lean_box((v___x_1550_) as usize);
        v___x_1558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1557_);
        return v___x_1558_;
    } else {
        let mut v___x_1559_: u8 = 0;
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1559_ = 0;
        v___x_1560_ = crate::leanh::lean_box((v___x_1559_) as usize);
        v___x_1561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
        return v___x_1561_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(
    mut v___x_1562_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319__boxed_1569_: u8 = 0;
    let mut v_____do__lift_2320__boxed_1570_: u8 = 0;
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319__boxed_1569_ = (crate::leanh::lean_unbox(v___x_1562_) as u8);
    v_____do__lift_2320__boxed_1570_ = (crate::leanh::lean_unbox(v_____do__lift_1563_) as u8);
    v_res_1571_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(
        v___x_2319__boxed_1569_,
        v_____do__lift_2320__boxed_1570_,
        v___y_1564_,
        v___y_1565_,
        v___y_1566_,
        v___y_1567_,
    );
    crate::leanh::lean_dec(v___y_1567_);
    crate::leanh::lean_dec_ref(v___y_1566_);
    crate::leanh::lean_dec(v___y_1565_);
    crate::leanh::lean_dec_ref(v___y_1564_);
    return v_res_1571_;
}
pub unsafe fn l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(
    mut v_x_1572_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1573_: u8 = 0;
    let mut v_head_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1572_) == 0 {
                    v___x_1573_ = 1;
                    return v___x_1573_;
                } else {
                    v_head_1574_ = crate::leanh::lean_ctor_get(v_x_1572_, 0);
                    v_tail_1575_ = crate::leanh::lean_ctor_get(v_x_1572_, 1);
                    v_fst_1576_ = crate::leanh::lean_ctor_get(v_head_1574_, 0);
                    v_snd_1577_ = crate::leanh::lean_ctor_get(v_head_1574_, 1);
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
    mut v_x_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1581_: u8 = 0;
    let mut v_r_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v_x_1580_);
    crate::leanh::lean_dec(v_x_1580_);
    v_r_1582_ = crate::leanh::lean_box((v_res_1581_) as usize);
    return v_r_1582_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(
    mut v___x_1583_: u8,
    mut v_as_1584_: *mut crate::leanh::LeanObject,
    mut v_i_1585_: usize,
    mut v_stop_1586_: usize,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v_a_1598_: u8 = 0;
    let mut v___x_1599_: usize = 0;
    let mut v___x_1600_: usize = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    let mut v_a_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = lean_usize_dec_eq(v_i_1585_, v_stop_1586_);
                if v___x_1592_ == 0 {
                    v___x_1593_ = lean_array_uget_borrowed(v_as_1584_, v_i_1585_);
                    v_fst_1594_ = crate::leanh::lean_ctor_get(v___x_1593_, 0);
                    v_snd_1595_ = crate::leanh::lean_ctor_get(v___x_1593_, 1);
                    v___x_1596_ = 1;
                    crate::leanh::lean_inc(v_snd_1595_);
                    crate::leanh::lean_inc(v_fst_1594_);
                    v___x_1604_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_fst_1594_,
                        v_snd_1595_,
                        v___y_1587_,
                        v___y_1588_,
                        v___y_1589_,
                        v___y_1590_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1604_) == 0 {
                        v_a_1605_ = crate::leanh::lean_ctor_get(v___x_1604_, 0);
                        crate::leanh::lean_inc(v_a_1605_);
                        crate::leanh::lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1606_ = (crate::leanh::lean_unbox(v_a_1605_) as u8);
                        crate::leanh::lean_dec(v_a_1605_);
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
                        if crate::leanh::lean_obj_tag(v___x_1604_) == 0 {
                            v_a_1607_ = crate::leanh::lean_ctor_get(v___x_1604_, 0);
                            crate::leanh::lean_inc(v_a_1607_);
                            crate::leanh::lean_dec_ref_known(v___x_1604_, 1);
                            v___x_1608_ = (crate::leanh::lean_unbox(v_a_1607_) as u8);
                            crate::leanh::lean_dec(v_a_1607_);
                            v_a_1598_ = v___x_1608_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_1604_;
                        }
                    }
                } else {
                    v___x_1609_ = 0;
                    v___x_1610_ = crate::leanh::lean_box((v___x_1609_) as usize);
                    v___x_1611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1611_, 0, v___x_1610_);
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
                    v___x_1602_ = crate::leanh::lean_box((v___x_1596_) as usize);
                    v___x_1603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
                    return v___x_1603_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(
    mut v___x_1612_: *mut crate::leanh::LeanObject,
    mut v_as_1613_: *mut crate::leanh::LeanObject,
    mut v_i_1614_: *mut crate::leanh::LeanObject,
    mut v_stop_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2367__boxed_1621_: u8 = 0;
    let mut v_i_boxed_1622_: usize = 0;
    let mut v_stop_boxed_1623_: usize = 0;
    let mut v_res_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2367__boxed_1621_ = (crate::leanh::lean_unbox(v___x_1612_) as u8);
    v_i_boxed_1622_ = crate::leanh::lean_unbox_usize(v_i_1614_);
    crate::leanh::lean_dec(v_i_1614_);
    v_stop_boxed_1623_ = crate::leanh::lean_unbox_usize(v_stop_1615_);
    crate::leanh::lean_dec(v_stop_1615_);
    v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_2367__boxed_1621_, v_as_1613_, v_i_boxed_1622_, v_stop_boxed_1623_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
    crate::leanh::lean_dec(v___y_1619_);
    crate::leanh::lean_dec_ref(v___y_1618_);
    crate::leanh::lean_dec(v___y_1617_);
    crate::leanh::lean_dec_ref(v___y_1616_);
    crate::leanh::lean_dec_ref(v_as_1613_);
    return v_res_1624_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_isDefEq(
    mut v_igi1_1625_: *mut crate::leanh::LeanObject,
    mut v_igi2_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toIndGroupInfo_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v_a_1649_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: usize = 0;
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toIndGroupInfo_1632_ = crate::leanh::lean_ctor_get(v_igi1_1625_, 0);
                crate::leanh::lean_inc_ref(v_toIndGroupInfo_1632_);
                v_levels_1633_ = crate::leanh::lean_ctor_get(v_igi1_1625_, 1);
                crate::leanh::lean_inc(v_levels_1633_);
                v_params_1634_ = crate::leanh::lean_ctor_get(v_igi1_1625_, 2);
                crate::leanh::lean_inc_ref(v_params_1634_);
                crate::leanh::lean_dec_ref(v_igi1_1625_);
                v_toIndGroupInfo_1635_ = crate::leanh::lean_ctor_get(v_igi2_1626_, 0);
                crate::leanh::lean_inc_ref(v_toIndGroupInfo_1635_);
                v_levels_1636_ = crate::leanh::lean_ctor_get(v_igi2_1626_, 1);
                crate::leanh::lean_inc(v_levels_1636_);
                v_params_1637_ = crate::leanh::lean_ctor_get(v_igi2_1626_, 2);
                crate::leanh::lean_inc_ref(v_params_1637_);
                crate::leanh::lean_dec_ref(v_igi2_1626_);
                v___x_1638_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(
                    v_toIndGroupInfo_1632_,
                    v_toIndGroupInfo_1635_,
                );
                crate::leanh::lean_dec_ref(v_toIndGroupInfo_1635_);
                crate::leanh::lean_dec_ref(v_toIndGroupInfo_1632_);
                if v___x_1638_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_1637_);
                    crate::leanh::lean_dec(v_levels_1636_);
                    crate::leanh::lean_dec_ref(v_params_1634_);
                    crate::leanh::lean_dec(v_levels_1633_);
                    v___x_1639_ = crate::leanh::lean_box((v___x_1638_) as usize);
                    v___x_1640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                    return v___x_1640_;
                } else {
                    v___x_1641_ = l_List_lengthTR___redArg(v_levels_1633_);
                    v___x_1642_ = l_List_lengthTR___redArg(v_levels_1636_);
                    v___x_1643_ = lean_nat_dec_eq(v___x_1641_, v___x_1642_);
                    crate::leanh::lean_dec(v___x_1642_);
                    crate::leanh::lean_dec(v___x_1641_);
                    if v___x_1643_ == 0 {
                        crate::leanh::lean_dec_ref(v_params_1637_);
                        crate::leanh::lean_dec(v_levels_1636_);
                        crate::leanh::lean_dec_ref(v_params_1634_);
                        crate::leanh::lean_dec(v_levels_1633_);
                        v___x_1644_ = crate::leanh::lean_box((v___x_1643_) as usize);
                        v___x_1645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                        return v___x_1645_;
                    } else {
                        v___x_1646_ = l_List_zipWith___at___00List_zip_spec__0(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_levels_1633_,
                            v_levels_1636_,
                        );
                        v___x_1647_ =
                            l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(
                                v___x_1646_,
                            );
                        crate::leanh::lean_dec(v___x_1646_);
                        if v___x_1647_ == 0 {
                            crate::leanh::lean_dec_ref(v_params_1637_);
                            crate::leanh::lean_dec_ref(v_params_1634_);
                            v___x_1658_ = crate::leanh::lean_box((v___x_1647_) as usize);
                            v___x_1659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                            return v___x_1659_;
                        } else {
                            v___x_1660_ = lean_array_get_size(v_params_1634_);
                            v___x_1661_ = lean_array_get_size(v_params_1637_);
                            v___x_1662_ = lean_nat_dec_eq(v___x_1660_, v___x_1661_);
                            if v___x_1662_ == 0 {
                                crate::leanh::lean_dec_ref(v_params_1637_);
                                crate::leanh::lean_dec_ref(v_params_1634_);
                                v___x_1663_ = crate::leanh::lean_box((v___x_1662_) as usize);
                                v___x_1664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
                                return v___x_1664_;
                            } else {
                                v___x_1665_ = l_Array_zip___redArg(v_params_1634_, v_params_1637_);
                                crate::leanh::lean_dec_ref(v_params_1637_);
                                crate::leanh::lean_dec_ref(v_params_1634_);
                                v___x_1666_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_1667_ = lean_array_get_size(v___x_1665_);
                                v___x_1668_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
                                if v___x_1668_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1665_);
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
                                        crate::leanh::lean_dec_ref(v___x_1665_);
                                        v_a_1649_ = v___x_1647_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1670_ = 0usize;
                                        v___x_1671_ = lean_usize_of_nat(v___x_1667_);
                                        v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_1647_, v___x_1665_, v___x_1670_, v___x_1671_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
                                        crate::leanh::lean_dec_ref(v___x_1665_);
                                        if crate::leanh::lean_obj_tag(v___x_1672_) == 0 {
                                            v_a_1673_ = crate::leanh::lean_ctor_get(v___x_1672_, 0);
                                            crate::leanh::lean_inc(v_a_1673_);
                                            crate::leanh::lean_dec_ref_known(v___x_1672_, 1);
                                            v___x_1674_ =
                                                (crate::leanh::lean_unbox(v_a_1673_) as u8);
                                            crate::leanh::lean_dec(v_a_1673_);
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
                    v___x_1650_ = crate::leanh::lean_box((v_a_1649_) as usize);
                    v___x_1651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1650_);
                    return v___x_1651_;
                } else {
                    v___x_1652_ = crate::leanh::lean_box((v___x_1647_) as usize);
                    v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1652_);
                    return v___x_1653_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1655_) == 0 {
                    v_a_1656_ = crate::leanh::lean_ctor_get(v___y_1655_, 0);
                    crate::leanh::lean_inc(v_a_1656_);
                    crate::leanh::lean_dec_ref_known(v___y_1655_, 1);
                    v___x_1657_ = (crate::leanh::lean_unbox(v_a_1656_) as u8);
                    crate::leanh::lean_dec(v_a_1656_);
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
    mut v_igi1_1676_: *mut crate::leanh::LeanObject,
    mut v_igi2_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v_a_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(
        v_igi1_1676_,
        v_igi2_1677_,
        v_a_1678_,
        v_a_1679_,
        v_a_1680_,
        v_a_1681_,
    );
    crate::leanh::lean_dec(v_a_1681_);
    crate::leanh::lean_dec_ref(v_a_1680_);
    crate::leanh::lean_dec(v_a_1679_);
    crate::leanh::lean_dec_ref(v_a_1678_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_brecOn(
    mut v_group_1684_: *mut crate::leanh::LeanObject,
    mut v_lvl_1685_: *mut crate::leanh::LeanObject,
    mut v_idx_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toIndGroupInfo_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toIndGroupInfo_1687_ = crate::leanh::lean_ctor_get(v_group_1684_, 0);
    v_levels_1688_ = crate::leanh::lean_ctor_get(v_group_1684_, 1);
    v_params_1689_ = crate::leanh::lean_ctor_get(v_group_1684_, 2);
    v_n_1690_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_1687_, v_idx_1686_);
    crate::leanh::lean_inc(v_levels_1688_);
    v_us_1691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_us_1691_, 0, v_lvl_1685_);
    crate::leanh::lean_ctor_set(v_us_1691_, 1, v_levels_1688_);
    v___x_1692_ = l_Lean_Expr_const___override(v_n_1690_, v_us_1691_);
    v___x_1693_ = l_Lean_mkAppN(v___x_1692_, v_params_1689_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(
    mut v_group_1694_: *mut crate::leanh::LeanObject,
    mut v_lvl_1695_: *mut crate::leanh::LeanObject,
    mut v_idx_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ =
        l_Lean_Elab_Structural_IndGroupInst_brecOn(v_group_1694_, v_lvl_1695_, v_idx_1696_);
    crate::leanh::lean_dec(v_idx_1696_);
    crate::leanh::lean_dec_ref(v_group_1694_);
    return v_res_1697_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
    mut v_msg_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988__overap_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1705_ =
        l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0;
    v___x_988__overap_1706_ = lean_panic_fn_borrowed(v___f_1705_, v_msg_1699_);
    crate::leanh::lean_inc(v___y_1703_);
    crate::leanh::lean_inc_ref(v___y_1702_);
    crate::leanh::lean_inc(v___y_1701_);
    crate::leanh::lean_inc_ref(v___y_1700_);
    v___x_1707_ = crate::leanh::lean_apply_5(
        v___x_988__overap_1706_,
        v___y_1700_,
        v___y_1701_,
        v___y_1702_,
        v___y_1703_,
        crate::leanh::lean_box(0),
    );
    return v___x_1707_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(
    mut v_msg_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
        v_msg_1708_,
        v___y_1709_,
        v___y_1710_,
        v___y_1711_,
        v___y_1712_,
    );
    crate::leanh::lean_dec(v___y_1712_);
    crate::leanh::lean_dec_ref(v___y_1711_);
    crate::leanh::lean_dec(v___y_1710_);
    crate::leanh::lean_dec_ref(v___y_1709_);
    return v_res_1714_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(
    mut v_k_1715_: *mut crate::leanh::LeanObject,
    mut v_b_1716_: *mut crate::leanh::LeanObject,
    mut v_c_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1721_);
    crate::leanh::lean_inc_ref(v___y_1720_);
    crate::leanh::lean_inc(v___y_1719_);
    crate::leanh::lean_inc_ref(v___y_1718_);
    v___x_1723_ = crate::leanh::lean_apply_7(
        v_k_1715_,
        v_b_1716_,
        v_c_1717_,
        v___y_1718_,
        v___y_1719_,
        v___y_1720_,
        v___y_1721_,
        crate::leanh::lean_box(0),
    );
    return v___x_1723_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(
    mut v_k_1724_: *mut crate::leanh::LeanObject,
    mut v_b_1725_: *mut crate::leanh::LeanObject,
    mut v_c_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_1724_, v_b_1725_, v_c_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
    crate::leanh::lean_dec(v___y_1730_);
    crate::leanh::lean_dec_ref(v___y_1729_);
    crate::leanh::lean_dec(v___y_1728_);
    crate::leanh::lean_dec_ref(v___y_1727_);
    return v_res_1732_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(
    mut v_type_1733_: *mut crate::leanh::LeanObject,
    mut v_k_1734_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1735_: u8,
    mut v_whnfType_1736_: u8,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_a_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1755_: u8 = 0;
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1742_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1742_, 0, v_k_1734_);
                v___x_1743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1733_,
                    v___f_1742_,
                    v_cleanupAnnotations_1735_,
                    v_whnfType_1736_,
                    v___y_1737_,
                    v___y_1738_,
                    v___y_1739_,
                    v___y_1740_,
                );
                if crate::leanh::lean_obj_tag(v___x_1743_) == 0 {
                    v_a_1744_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                    v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v___x_1743_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1746_ = v___x_1743_;
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1744_);
                        crate::leanh::lean_dec(v___x_1743_);
                        v___x_1746_ = crate::leanh::lean_box(0);
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1752_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                    v_isSharedCheck_1759_ = (!crate::leanh::lean_is_exclusive(v___x_1743_)) as u8;
                    if v_isSharedCheck_1759_ == 0 {
                        v___x_1754_ = v___x_1743_;
                        v_isShared_1755_ = v_isSharedCheck_1759_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1752_);
                        crate::leanh::lean_dec(v___x_1743_);
                        v___x_1754_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
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
                    v_reuseFailAlloc_1758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
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
    mut v_type_1760_: *mut crate::leanh::LeanObject,
    mut v_k_1761_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1762_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1763_: *mut crate::leanh::LeanObject,
    mut v___y_1764_: *mut crate::leanh::LeanObject,
    mut v___y_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1769_: u8 = 0;
    let mut v_whnfType_boxed_1770_: u8 = 0;
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1769_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1762_) as u8);
    v_whnfType_boxed_1770_ = (crate::leanh::lean_unbox(v_whnfType_1763_) as u8);
    v_res_1771_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_1760_, v_k_1761_, v_cleanupAnnotations_boxed_1769_, v_whnfType_boxed_1770_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
    crate::leanh::lean_dec(v___y_1767_);
    crate::leanh::lean_dec_ref(v___y_1766_);
    crate::leanh::lean_dec(v___y_1765_);
    crate::leanh::lean_dec_ref(v___y_1764_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(
    mut v_00_u03b1_1772_: *mut crate::leanh::LeanObject,
    mut v_type_1773_: *mut crate::leanh::LeanObject,
    mut v_k_1774_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1775_: u8,
    mut v_whnfType_1776_: u8,
    mut v___y_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_1773_, v_k_1774_, v_cleanupAnnotations_1775_, v_whnfType_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(
    mut v_00_u03b1_1783_: *mut crate::leanh::LeanObject,
    mut v_type_1784_: *mut crate::leanh::LeanObject,
    mut v_k_1785_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1786_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1793_: u8 = 0;
    let mut v_whnfType_boxed_1794_: u8 = 0;
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1793_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1786_) as u8);
    v_whnfType_boxed_1794_ = (crate::leanh::lean_unbox(v_whnfType_1787_) as u8);
    v_res_1795_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(v_00_u03b1_1783_, v_type_1784_, v_k_1785_, v_cleanupAnnotations_boxed_1793_, v_whnfType_boxed_1794_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
    crate::leanh::lean_dec(v___y_1791_);
    crate::leanh::lean_dec_ref(v___y_1790_);
    crate::leanh::lean_dec(v___y_1789_);
    crate::leanh::lean_dec_ref(v___y_1788_);
    return v_res_1795_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(
    mut v_msg_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050__overap_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1802_ =
        l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0;
    v___x_2050__overap_1803_ = lean_panic_fn_borrowed(v___f_1802_, v_msg_1796_);
    crate::leanh::lean_inc(v___y_1800_);
    crate::leanh::lean_inc_ref(v___y_1799_);
    crate::leanh::lean_inc(v___y_1798_);
    crate::leanh::lean_inc_ref(v___y_1797_);
    v___x_1804_ = crate::leanh::lean_apply_5(
        v___x_2050__overap_1803_,
        v___y_1797_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        crate::leanh::lean_box(0),
    );
    return v___x_1804_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(
    mut v_msg_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(
        v_msg_1805_,
        v___y_1806_,
        v___y_1807_,
        v___y_1808_,
        v___y_1809_,
    );
    crate::leanh::lean_dec(v___y_1809_);
    crate::leanh::lean_dec_ref(v___y_1808_);
    crate::leanh::lean_dec(v___y_1807_);
    crate::leanh::lean_dec_ref(v___y_1806_);
    return v_res_1811_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2;
    v___x_1816_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1817_ = crate::leanh::lean_unsigned_to_nat(113);
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
    mut v___x_1821_: *mut crate::leanh::LeanObject,
    mut v_xs_1822_: *mut crate::leanh::LeanObject,
    mut v_x_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    v___x_1829_ = lean_array_get_size(v_xs_1822_);
    v___x_1830_ = lean_nat_dec_lt(v___x_1821_, v___x_1829_);
    if v___x_1830_ == 0 {
        let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1822_);
        v___x_1831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3);
        v___x_1832_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(
            v___x_1831_,
            v___y_1824_,
            v___y_1825_,
            v___y_1826_,
            v___y_1827_,
        );
        return v___x_1832_;
    } else {
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1833_ = l_Lean_instInhabitedExpr;
        v___x_1834_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1835_ = lean_nat_sub(v___x_1829_, v___x_1834_);
        v___x_1836_ = lean_array_get_borrowed(v___x_1833_, v_xs_1822_, v___x_1835_);
        crate::leanh::lean_dec(v___x_1835_);
        crate::leanh::lean_inc(v___y_1827_);
        crate::leanh::lean_inc_ref(v___y_1826_);
        crate::leanh::lean_inc(v___y_1825_);
        crate::leanh::lean_inc_ref(v___y_1824_);
        crate::leanh::lean_inc(v___x_1836_);
        v___x_1837_ = lean_infer_type(
            v___x_1836_,
            v___y_1824_,
            v___y_1825_,
            v___y_1826_,
            v___y_1827_,
        );
        if crate::leanh::lean_obj_tag(v___x_1837_) == 0 {
            let mut v_a_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1840_: u8 = 0;
            let mut v___x_1841_: u8 = 0;
            let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1838_ = crate::leanh::lean_ctor_get(v___x_1837_, 0);
            crate::leanh::lean_inc(v_a_1838_);
            crate::leanh::lean_dec_ref_known(v___x_1837_, 1);
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
            crate::leanh::lean_dec_ref(v___x_1839_);
            return v___x_1842_;
        } else {
            crate::leanh::lean_dec_ref(v_xs_1822_);
            return v___x_1837_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(
    mut v___x_1843_: *mut crate::leanh::LeanObject,
    mut v_xs_1844_: *mut crate::leanh::LeanObject,
    mut v_x_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_1843_, v_xs_1844_, v_x_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    crate::leanh::lean_dec(v___y_1847_);
    crate::leanh::lean_dec_ref(v___y_1846_);
    crate::leanh::lean_dec_ref(v_x_1845_);
    crate::leanh::lean_dec(v___x_1843_);
    return v_res_1851_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(
    mut v_sz_1854_: usize,
    mut v_i_1855_: usize,
    mut v_bs_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: usize = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1862_ = lean_usize_dec_lt(v_i_1855_, v_sz_1854_);
                if v___x_1862_ == 0 {
                    v___x_1863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1863_, 0, v_bs_1856_);
                    return v___x_1863_;
                } else {
                    v___x_1864_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___f_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0;
                    v_v_1866_ = lean_array_uget_borrowed(v_bs_1856_, v_i_1855_);
                    v___x_1867_ = 0;
                    crate::leanh::lean_inc(v_v_1866_);
                    v___x_1868_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_v_1866_, v___f_1865_, v___x_1867_, v___x_1867_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
                    if crate::leanh::lean_obj_tag(v___x_1868_) == 0 {
                        v_a_1869_ = crate::leanh::lean_ctor_get(v___x_1868_, 0);
                        crate::leanh::lean_inc(v_a_1869_);
                        crate::leanh::lean_dec_ref_known(v___x_1868_, 1);
                        v_bs_x27_1870_ = lean_array_uset(v_bs_1856_, v_i_1855_, v___x_1864_);
                        v___x_1871_ = 1usize;
                        v___x_1872_ = lean_usize_add(v_i_1855_, v___x_1871_);
                        v___x_1873_ = lean_array_uset(v_bs_x27_1870_, v_i_1855_, v_a_1869_);
                        v_i_1855_ = v___x_1872_;
                        v_bs_1856_ = v___x_1873_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1856_);
                        v_a_1875_ = crate::leanh::lean_ctor_get(v___x_1868_, 0);
                        v_isSharedCheck_1882_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1868_)) as u8;
                        if v_isSharedCheck_1882_ == 0 {
                            v___x_1877_ = v___x_1868_;
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1875_);
                            crate::leanh::lean_dec(v___x_1868_);
                            v___x_1877_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
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
    mut v_sz_1883_: *mut crate::leanh::LeanObject,
    mut v_i_1884_: *mut crate::leanh::LeanObject,
    mut v_bs_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1891_: usize = 0;
    let mut v_i_boxed_1892_: usize = 0;
    let mut v_res_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1891_ = crate::leanh::lean_unbox_usize(v_sz_1883_);
    crate::leanh::lean_dec(v_sz_1883_);
    v_i_boxed_1892_ = crate::leanh::lean_unbox_usize(v_i_1884_);
    crate::leanh::lean_dec(v_i_1884_);
    v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_sz_boxed_1891_, v_i_boxed_1892_, v_bs_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
    crate::leanh::lean_dec(v___y_1889_);
    crate::leanh::lean_dec_ref(v___y_1888_);
    crate::leanh::lean_dec(v___y_1887_);
    crate::leanh::lean_dec_ref(v___y_1886_);
    return v_res_1893_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1894_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(
    mut v_msg_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v_toFunctor_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___f_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v_toFunctor_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___f_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651__overap_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_unused_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_unused_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_unused_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_unused_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once), _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0);
                v___x_1906_ = l_StateRefT_x27_instMonad___redArg(v___x_1905_);
                v_toApplicative_1907_ = crate::leanh::lean_ctor_get(v___x_1906_, 0);
                v_isSharedCheck_1968_ = (!crate::leanh::lean_is_exclusive(v___x_1906_)) as u8;
                if v_isSharedCheck_1968_ == 0 {
                    v_unused_1969_ = crate::leanh::lean_ctor_get(v___x_1906_, 1);
                    crate::leanh::lean_dec(v_unused_1969_);
                    v___x_1909_ = v___x_1906_;
                    v_isShared_1910_ = v_isSharedCheck_1968_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1907_);
                    crate::leanh::lean_dec(v___x_1906_);
                    v___x_1909_ = crate::leanh::lean_box(0);
                    v_isShared_1910_ = v_isSharedCheck_1968_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1911_ = crate::leanh::lean_ctor_get(v_toApplicative_1907_, 0);
                v_toSeq_1912_ = crate::leanh::lean_ctor_get(v_toApplicative_1907_, 2);
                v_toSeqLeft_1913_ = crate::leanh::lean_ctor_get(v_toApplicative_1907_, 3);
                v_toSeqRight_1914_ = crate::leanh::lean_ctor_get(v_toApplicative_1907_, 4);
                v_isSharedCheck_1966_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1907_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v_unused_1967_ = crate::leanh::lean_ctor_get(v_toApplicative_1907_, 1);
                    crate::leanh::lean_dec(v_unused_1967_);
                    v___x_1916_ = v_toApplicative_1907_;
                    v_isShared_1917_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1914_);
                    crate::leanh::lean_inc(v_toSeqLeft_1913_);
                    crate::leanh::lean_inc(v_toSeq_1912_);
                    crate::leanh::lean_inc(v_toFunctor_1911_);
                    crate::leanh::lean_dec(v_toApplicative_1907_);
                    v___x_1916_ = crate::leanh::lean_box(0);
                    v_isShared_1917_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1918_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1;
                v___f_1919_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1911_);
                v___f_1920_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1920_, 0, v_toFunctor_1911_);
                v___f_1921_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1921_, 0, v_toFunctor_1911_);
                v___x_1922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1922_, 0, v___f_1920_);
                crate::leanh::lean_ctor_set(v___x_1922_, 1, v___f_1921_);
                v___f_1923_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1923_, 0, v_toSeqRight_1914_);
                v___f_1924_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1924_, 0, v_toSeqLeft_1913_);
                v___f_1925_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1925_, 0, v_toSeq_1912_);
                if v_isShared_1917_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1916_, 4, v___f_1923_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 3, v___f_1924_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 2, v___f_1925_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 1, v___f_1918_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1922_);
                    v___x_1927_ = v___x_1916_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___f_1918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 2, v___f_1925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 3, v___f_1924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 4, v___f_1923_);
                    v___x_1927_ = v_reuseFailAlloc_1965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1910_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1909_, 1, v___f_1919_);
                    crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1927_);
                    v___x_1929_ = v___x_1909_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___f_1919_);
                    v___x_1929_ = v_reuseFailAlloc_1964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1930_ = l_StateRefT_x27_instMonad___redArg(v___x_1929_);
                v_toApplicative_1931_ = crate::leanh::lean_ctor_get(v___x_1930_, 0);
                v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v___x_1930_)) as u8;
                if v_isSharedCheck_1962_ == 0 {
                    v_unused_1963_ = crate::leanh::lean_ctor_get(v___x_1930_, 1);
                    crate::leanh::lean_dec(v_unused_1963_);
                    v___x_1933_ = v___x_1930_;
                    v_isShared_1934_ = v_isSharedCheck_1962_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1931_);
                    crate::leanh::lean_dec(v___x_1930_);
                    v___x_1933_ = crate::leanh::lean_box(0);
                    v_isShared_1934_ = v_isSharedCheck_1962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1935_ = crate::leanh::lean_ctor_get(v_toApplicative_1931_, 0);
                v_toSeq_1936_ = crate::leanh::lean_ctor_get(v_toApplicative_1931_, 2);
                v_toSeqLeft_1937_ = crate::leanh::lean_ctor_get(v_toApplicative_1931_, 3);
                v_toSeqRight_1938_ = crate::leanh::lean_ctor_get(v_toApplicative_1931_, 4);
                v_isSharedCheck_1960_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1931_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v_unused_1961_ = crate::leanh::lean_ctor_get(v_toApplicative_1931_, 1);
                    crate::leanh::lean_dec(v_unused_1961_);
                    v___x_1940_ = v_toApplicative_1931_;
                    v_isShared_1941_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1938_);
                    crate::leanh::lean_inc(v_toSeqLeft_1937_);
                    crate::leanh::lean_inc(v_toSeq_1936_);
                    crate::leanh::lean_inc(v_toFunctor_1935_);
                    crate::leanh::lean_dec(v_toApplicative_1931_);
                    v___x_1940_ = crate::leanh::lean_box(0);
                    v_isShared_1941_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1942_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3;
                v___f_1943_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1935_);
                v___f_1944_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1944_, 0, v_toFunctor_1935_);
                v___f_1945_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1945_, 0, v_toFunctor_1935_);
                v___x_1946_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1946_, 0, v___f_1944_);
                crate::leanh::lean_ctor_set(v___x_1946_, 1, v___f_1945_);
                v___f_1947_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1947_, 0, v_toSeqRight_1938_);
                v___f_1948_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1948_, 0, v_toSeqLeft_1937_);
                v___f_1949_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1949_, 0, v_toSeq_1936_);
                if v_isShared_1941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1940_, 4, v___f_1947_);
                    crate::leanh::lean_ctor_set(v___x_1940_, 3, v___f_1948_);
                    crate::leanh::lean_ctor_set(v___x_1940_, 2, v___f_1949_);
                    crate::leanh::lean_ctor_set(v___x_1940_, 1, v___f_1942_);
                    crate::leanh::lean_ctor_set(v___x_1940_, 0, v___x_1946_);
                    v___x_1951_ = v___x_1940_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___f_1942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___f_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 3, v___f_1948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___f_1947_);
                    v___x_1951_ = v_reuseFailAlloc_1959_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1933_, 1, v___f_1943_);
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1933_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___f_1943_);
                    v___x_1953_ = v_reuseFailAlloc_1958_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1954_ = crate::leanh::lean_box(0);
                v___x_1955_ = l_instInhabitedOfMonad___redArg(v___x_1953_, v___x_1954_);
                v___x_2651__overap_1956_ = lean_panic_fn_borrowed(v___x_1955_, v_msg_1899_);
                crate::leanh::lean_dec(v___x_1955_);
                crate::leanh::lean_inc(v___y_1903_);
                crate::leanh::lean_inc_ref(v___y_1902_);
                crate::leanh::lean_inc(v___y_1901_);
                crate::leanh::lean_inc_ref(v___y_1900_);
                v___x_1957_ = crate::leanh::lean_apply_5(
                    v___x_2651__overap_1956_,
                    v___y_1900_,
                    v___y_1901_,
                    v___y_1902_,
                    v___y_1903_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(
    mut v_msg_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
    crate::leanh::lean_dec(v___y_1974_);
    crate::leanh::lean_dec_ref(v___y_1973_);
    crate::leanh::lean_dec(v___y_1972_);
    crate::leanh::lean_dec_ref(v___y_1971_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(
    mut v_msgData_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = lean_st_ref_get(v___y_1981_);
    v_env_1984_ = crate::leanh::lean_ctor_get(v___x_1983_, 0);
    crate::leanh::lean_inc_ref(v_env_1984_);
    crate::leanh::lean_dec(v___x_1983_);
    v___x_1985_ = lean_st_ref_get(v___y_1979_);
    v_mctx_1986_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1986_);
    crate::leanh::lean_dec(v___x_1985_);
    v_lctx_1987_ = crate::leanh::lean_ctor_get(v___y_1978_, 2);
    v_options_1988_ = crate::leanh::lean_ctor_get(v___y_1980_, 2);
    crate::leanh::lean_inc_ref(v_options_1988_);
    crate::leanh::lean_inc_ref(v_lctx_1987_);
    v___x_1989_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1989_, 0, v_env_1984_);
    crate::leanh::lean_ctor_set(v___x_1989_, 1, v_mctx_1986_);
    crate::leanh::lean_ctor_set(v___x_1989_, 2, v_lctx_1987_);
    crate::leanh::lean_ctor_set(v___x_1989_, 3, v_options_1988_);
    v___x_1990_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1990_, 0, v___x_1989_);
    crate::leanh::lean_ctor_set(v___x_1990_, 1, v_msgData_1977_);
    v___x_1991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_1990_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(
    mut v_msgData_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
    crate::leanh::lean_dec(v___y_1996_);
    crate::leanh::lean_dec_ref(v___y_1995_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(
    mut v_msg_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2005_ = crate::leanh::lean_ctor_get(v___y_2002_, 5);
                v___x_2006_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
                v_a_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                v_isSharedCheck_2015_ = (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                if v_isSharedCheck_2015_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2007_);
                    crate::leanh::lean_dec(v___x_2006_);
                    v___x_2009_ = crate::leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2005_);
                v___x_2011_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2011_, 0, v_ref_2005_);
                crate::leanh::lean_ctor_set(v___x_2011_, 1, v_a_2007_);
                if v_isShared_2010_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2009_, 1);
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2011_);
                    v___x_2013_ = v___x_2009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
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
    mut v_msg_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
    crate::leanh::lean_dec(v___y_2020_);
    crate::leanh::lean_dec_ref(v___y_2019_);
    crate::leanh::lean_dec(v___y_2018_);
    crate::leanh::lean_dec_ref(v___y_2017_);
    return v_res_2022_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0;
    v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2;
    v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6;
    v___x_2033_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2034_ = crate::leanh::lean_unsigned_to_nat(129);
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
    mut v_constName_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v_val_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_a_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_st_ref_get(v___y_2042_);
                v_env_2053_ = crate::leanh::lean_ctor_get(v___x_2052_, 0);
                crate::leanh::lean_inc_ref(v_env_2053_);
                crate::leanh::lean_dec(v___x_2052_);
                v___x_2054_ = 0;
                crate::leanh::lean_inc(v_constName_2038_);
                v___x_2055_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2053_, v_constName_2038_, v___x_2054_);
                if crate::leanh::lean_obj_tag(v___x_2055_) == 1 {
                    v_val_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    crate::leanh::lean_inc(v_val_2056_);
                    crate::leanh::lean_dec_ref_known(v___x_2055_, 1);
                    v_kind_2057_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2056_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2057_ == 7 {
                        v___x_2058_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2056_);
                        if crate::leanh::lean_obj_tag(v___x_2058_) == 7 {
                            crate::leanh::lean_dec(v_constName_2038_);
                            v_val_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                            v_isSharedCheck_2066_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2058_)) as u8;
                            if v_isSharedCheck_2066_ == 0 {
                                v___x_2061_ = v___x_2058_;
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2059_);
                                crate::leanh::lean_dec(v___x_2058_);
                                v___x_2061_ = crate::leanh::lean_box(0);
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2058_);
                            v___x_2067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7);
                            v___x_2068_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v___x_2067_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                            if crate::leanh::lean_obj_tag(v___x_2068_) == 0 {
                                v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                                v_isSharedCheck_2077_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2068_)) as u8;
                                if v_isSharedCheck_2077_ == 0 {
                                    v___x_2071_ = v___x_2068_;
                                    v_isShared_2072_ = v_isSharedCheck_2077_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2069_);
                                    crate::leanh::lean_dec(v___x_2068_);
                                    v___x_2071_ = crate::leanh::lean_box(0);
                                    v_isShared_2072_ = v_isSharedCheck_2077_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_2038_);
                                v_a_2078_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                                v_isSharedCheck_2085_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2068_)) as u8;
                                if v_isSharedCheck_2085_ == 0 {
                                    v___x_2080_ = v___x_2068_;
                                    v_isShared_2081_ = v_isSharedCheck_2085_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2078_);
                                    crate::leanh::lean_dec(v___x_2068_);
                                    v___x_2080_ = crate::leanh::lean_box(0);
                                    v_isShared_2081_ = v_isSharedCheck_2085_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2056_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2055_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2045_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1);
                v___x_2046_ = 0;
                v___x_2047_ = l_Lean_MessageData_ofConstName(v_constName_2038_, v___x_2046_);
                v___x_2048_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2048_, 0, v___x_2045_);
                crate::leanh::lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                v___x_2049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once), _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3);
                v___x_2050_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2048_);
                crate::leanh::lean_ctor_set(v___x_2050_, 1, v___x_2049_);
                v___x_2051_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v___x_2050_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                return v___x_2051_;
            }
            2 => {
                if v_isShared_2062_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2061_, 0);
                    v___x_2064_ = v___x_2061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_val_2059_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2064_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2069_) == 0 {
                    crate::leanh::lean_del_object(v___x_2071_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_2038_);
                    v_val_2073_ = crate::leanh::lean_ctor_get(v_a_2069_, 0);
                    crate::leanh::lean_inc(v_val_2073_);
                    crate::leanh::lean_dec_ref_known(v_a_2069_, 1);
                    if v_isShared_2072_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2071_, 0, v_val_2073_);
                        v___x_2075_ = v___x_2071_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_val_2073_);
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
                    v_reuseFailAlloc_2084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
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
    mut v_constName_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
    mut v___y_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
    mut v___y_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ =
        l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(
            v_constName_2086_,
            v___y_2087_,
            v___y_2088_,
            v___y_2089_,
            v___y_2090_,
        );
    crate::leanh::lean_dec(v___y_2090_);
    crate::leanh::lean_dec_ref(v___y_2089_);
    crate::leanh::lean_dec(v___y_2088_);
    crate::leanh::lean_dec_ref(v___y_2087_);
    return v_res_2092_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0;
    v___x_2095_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2096_ = crate::leanh::lean_unsigned_to_nat(104);
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
    mut v_igi_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levels_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recName_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_unused_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toIndGroupInfo_2117_ = crate::leanh::lean_ctor_get(v_igi_2102_, 0);
                crate::leanh::lean_inc_ref(v_toIndGroupInfo_2117_);
                v_levels_2118_ = crate::leanh::lean_ctor_get(v_igi_2102_, 1);
                crate::leanh::lean_inc(v_levels_2118_);
                v_params_2119_ = crate::leanh::lean_ctor_get(v_igi_2102_, 2);
                crate::leanh::lean_inc_ref(v_params_2119_);
                crate::leanh::lean_dec_ref(v_igi_2102_);
                v_all_2120_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 0);
                crate::leanh::lean_inc_ref(v_all_2120_);
                v_numNested_2121_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 1);
                v___x_2122_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2123_ = lean_nat_dec_eq(v_numNested_2121_, v___x_2122_);
                if v___x_2123_ == 0 {
                    v___x_2124_ = crate::leanh::lean_box(0);
                    v___x_2125_ = lean_array_get_borrowed(v___x_2124_, v_all_2120_, v___x_2122_);
                    crate::leanh::lean_inc(v___x_2125_);
                    v_recName_2126_ = l_Lean_mkRecName(v___x_2125_);
                    crate::leanh::lean_inc(v_recName_2126_);
                    v___x_2127_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_recName_2126_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                    if crate::leanh::lean_obj_tag(v___x_2127_) == 0 {
                        v_a_2128_ = crate::leanh::lean_ctor_get(v___x_2127_, 0);
                        crate::leanh::lean_inc(v_a_2128_);
                        crate::leanh::lean_dec_ref_known(v___x_2127_, 1);
                        v_toConstantVal_2129_ = crate::leanh::lean_ctor_get(v_a_2128_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_2129_);
                        v_numMotives_2130_ = crate::leanh::lean_ctor_get(v_a_2128_, 4);
                        crate::leanh::lean_inc(v_numMotives_2130_);
                        crate::leanh::lean_dec(v_a_2128_);
                        v___x_2140_ =
                            l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_2117_);
                        v_isSharedCheck_2155_ =
                            (!crate::leanh::lean_is_exclusive(v_toIndGroupInfo_2117_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v_unused_2156_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 1);
                            crate::leanh::lean_dec(v_unused_2156_);
                            v_unused_2157_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_2117_, 0);
                            crate::leanh::lean_dec(v_unused_2157_);
                            v___x_2142_ = v_toIndGroupInfo_2117_;
                            v_isShared_2143_ = v_isSharedCheck_2155_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_toIndGroupInfo_2117_);
                            v___x_2142_ = crate::leanh::lean_box(0);
                            v_isShared_2143_ = v_isSharedCheck_2155_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_recName_2126_);
                        crate::leanh::lean_dec_ref(v_all_2120_);
                        crate::leanh::lean_dec_ref(v_params_2119_);
                        crate::leanh::lean_dec(v_levels_2118_);
                        crate::leanh::lean_dec_ref(v_toIndGroupInfo_2117_);
                        v_a_2158_ = crate::leanh::lean_ctor_get(v___x_2127_, 0);
                        v_isSharedCheck_2165_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2127_)) as u8;
                        if v_isSharedCheck_2165_ == 0 {
                            v___x_2160_ = v___x_2127_;
                            v_isShared_2161_ = v_isSharedCheck_2165_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2158_);
                            crate::leanh::lean_dec(v___x_2127_);
                            v___x_2160_ = crate::leanh::lean_box(0);
                            v_isShared_2161_ = v_isSharedCheck_2165_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_all_2120_);
                    crate::leanh::lean_dec_ref(v_params_2119_);
                    crate::leanh::lean_dec(v_levels_2118_);
                    crate::leanh::lean_dec_ref(v_toIndGroupInfo_2117_);
                    v___x_2166_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2;
                    v___x_2167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2167_, 0, v___x_2166_);
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
                crate::leanh::lean_dec_ref(v_params_2119_);
                v___x_2135_ = l_Lean_Meta_inferArgumentTypesN(
                    v_numMotives_2130_,
                    v___x_2134_,
                    v_a_2103_,
                    v_a_2104_,
                    v_a_2105_,
                    v_a_2106_,
                );
                if crate::leanh::lean_obj_tag(v___x_2135_) == 0 {
                    v_a_2136_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                    crate::leanh::lean_inc(v_a_2136_);
                    crate::leanh::lean_dec_ref_known(v___x_2135_, 1);
                    v___x_2137_ = lean_array_get_size(v_all_2120_);
                    crate::leanh::lean_dec_ref(v_all_2120_);
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
                    crate::leanh::lean_dec_ref(v_all_2120_);
                    return v___x_2135_;
                }
            }
            3 => {
                v___x_2144_ = lean_nat_dec_eq(v_numMotives_2130_, v___x_2140_);
                crate::leanh::lean_dec(v___x_2140_);
                if v___x_2144_ == 0 {
                    crate::leanh::lean_del_object(v___x_2142_);
                    crate::leanh::lean_dec(v_numMotives_2130_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_2129_);
                    crate::leanh::lean_dec(v_recName_2126_);
                    crate::leanh::lean_dec_ref(v_all_2120_);
                    crate::leanh::lean_dec_ref(v_params_2119_);
                    crate::leanh::lean_dec(v_levels_2118_);
                    v___x_2145_ = crate::leanh::lean_obj_once(
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
                    v_levelParams_2147_ = crate::leanh::lean_ctor_get(v_toConstantVal_2129_, 1);
                    crate::leanh::lean_inc(v_levelParams_2147_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_2129_);
                    v___x_2148_ = l_List_lengthTR___redArg(v_levels_2118_);
                    v___x_2149_ = l_List_lengthTR___redArg(v_levelParams_2147_);
                    crate::leanh::lean_dec(v_levelParams_2147_);
                    v___x_2150_ = lean_nat_dec_eq(v___x_2148_, v___x_2149_);
                    crate::leanh::lean_dec(v___x_2149_);
                    crate::leanh::lean_dec(v___x_2148_);
                    if v___x_2150_ == 0 {
                        v___x_2151_ = crate::leanh::lean_box(0);
                        if v_isShared_2143_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2142_, 1);
                            crate::leanh::lean_ctor_set(v___x_2142_, 1, v_levels_2118_);
                            crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2151_);
                            v___x_2153_ = v___x_2142_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2154_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_levels_2118_);
                            v___x_2153_ = v_reuseFailAlloc_2154_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2142_);
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
                    v_reuseFailAlloc_2164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
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
    mut v_igi_2168_: *mut crate::leanh::LeanObject,
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(
        v_igi_2168_,
        v_a_2169_,
        v_a_2170_,
        v_a_2171_,
        v_a_2172_,
    );
    crate::leanh::lean_dec(v_a_2172_);
    crate::leanh::lean_dec_ref(v_a_2171_);
    crate::leanh::lean_dec(v_a_2170_);
    crate::leanh::lean_dec_ref(v_a_2169_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(
    mut v_00_u03b1_2175_: *mut crate::leanh::LeanObject,
    mut v_msg_2176_: *mut crate::leanh::LeanObject,
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v___y_2178_: *mut crate::leanh::LeanObject,
    mut v___y_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
    return v___x_2182_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(
    mut v_00_u03b1_2183_: *mut crate::leanh::LeanObject,
    mut v_msg_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(v_00_u03b1_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
    crate::leanh::lean_dec(v___y_2188_);
    crate::leanh::lean_dec_ref(v___y_2187_);
    crate::leanh::lean_dec(v___y_2186_);
    crate::leanh::lean_dec_ref(v___y_2185_);
    return v_res_2190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
}
