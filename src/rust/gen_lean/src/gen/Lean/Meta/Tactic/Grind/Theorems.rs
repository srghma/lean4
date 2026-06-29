// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Theorems
// Imports: Lean.HeadIndex Lean.Meta.Basic Lean.Meta.Eqns Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int, lean_st_ref_get,
    lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_eraseIdx___redArg,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_reprPrec, l_Lean_Syntax_instRepr_repr};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_erase___redArg,
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_constName_x21, l_Lean_Expr_isConst, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::HeadIndex::{initialize_Lean_HeadIndex, runtime_initialize_Lean_HeadIndex};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instAddMessageContextMetaM,
    l_Lean_Meta_instMonadEnvMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_mkConstWithFreshMVarLevels,
    l_Lean_Meta_mkFreshLevelMVar, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_getEqnsFor_x3f, runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::MonadEnv::l_Lean_getConstVal___redArg;
use crate::r#gen::Lean::OriginalConstKind::l_Lean_wasOriginallyTheorem;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParamsArray;
pub static l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedOrigin_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedOrigin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 105, 103,
        105, 110, 46, 100, 101, 99, 108, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 105, 103,
        105, 110, 46, 102, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value: crate::leanh::LeanStringObject<
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 105, 103,
        105, 110, 46, 115, 116, 120, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 105, 103,
        105, 110, 46, 108, 111, 99, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprOrigin_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprOrigin___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instReprOrigin_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instReprOrigin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instReprOrigin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instBEqOrigin___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instBEqOrigin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqOrigin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0: u64 = 0;
pub static l_Lean_Meta_Grind_instHashableOrigin___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instHashableOrigin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instHashableOrigin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableOrigin___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instInhabitedTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
        110, 100, 46, 84, 104, 101, 111, 114, 101, 109, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 84, 104, 101, 111,
        114, 101, 109, 115, 46, 105, 110, 115, 101, 114, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value:
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
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 119, 105, 116,
        104, 32, 116, 104, 101, 32, 96, 91, 103, 114, 105, 110, 100, 93, 96, 32, 97, 116, 116, 114,
        105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_getProofForDecl___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 104,
            101, 111, 114, 101, 109, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getProofForDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofForDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getProofForDecl___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_getProofForDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_getProofForDecl___closed__2_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            96, 44, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114,
            111, 112, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getProofForDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getProofForDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getProofForDecl___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_getProofForDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0_value:
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
static mut l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Origin_ctorIdx(
    mut v_x_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2416_) {
        0 => {
            let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2417_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2417_;
        }
        1 => {
            let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2418_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2418_;
        }
        2 => {
            let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2419_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2419_;
        }
        _ => {
            let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2420_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2420_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Origin_ctorIdx___boxed(
    mut v_x_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2422_ = l_Lean_Meta_Grind_Origin_ctorIdx(v_x_2421_);
    crate::leanh::lean_dec_ref(v_x_2421_);
    return v_res_2422_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_ctorElim___redArg(
    mut v_t_2423_: *mut crate::leanh::LeanObject,
    mut v_k_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2423_) == 2 {
        let mut v_id_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_id_2425_ = crate::leanh::lean_ctor_get(v_t_2423_, 0);
        crate::leanh::lean_inc(v_id_2425_);
        v_ref_2426_ = crate::leanh::lean_ctor_get(v_t_2423_, 1);
        crate::leanh::lean_inc(v_ref_2426_);
        crate::leanh::lean_dec_ref_known(v_t_2423_, 2);
        v___x_2427_ = crate::leanh::lean_apply_2(v_k_2424_, v_id_2425_, v_ref_2426_);
        return v___x_2427_;
    } else {
        let mut v_declName_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_2428_ = crate::leanh::lean_ctor_get(v_t_2423_, 0);
        crate::leanh::lean_inc(v_declName_2428_);
        crate::leanh::lean_dec_ref(v_t_2423_);
        v___x_2429_ = crate::leanh::lean_apply_1(v_k_2424_, v_declName_2428_);
        return v___x_2429_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Origin_ctorElim(
    mut v_motive_2430_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2431_: *mut crate::leanh::LeanObject,
    mut v_t_2432_: *mut crate::leanh::LeanObject,
    mut v_h_2433_: *mut crate::leanh::LeanObject,
    mut v_k_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2432_, v_k_2434_);
    return v___x_2435_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_ctorElim___boxed(
    mut v_motive_2436_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2437_: *mut crate::leanh::LeanObject,
    mut v_t_2438_: *mut crate::leanh::LeanObject,
    mut v_h_2439_: *mut crate::leanh::LeanObject,
    mut v_k_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l_Lean_Meta_Grind_Origin_ctorElim(
        v_motive_2436_,
        v_ctorIdx_2437_,
        v_t_2438_,
        v_h_2439_,
        v_k_2440_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2437_);
    return v_res_2441_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_decl_elim___redArg(
    mut v_t_2442_: *mut crate::leanh::LeanObject,
    mut v_decl_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2442_, v_decl_2443_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_decl_elim(
    mut v_motive_2445_: *mut crate::leanh::LeanObject,
    mut v_t_2446_: *mut crate::leanh::LeanObject,
    mut v_h_2447_: *mut crate::leanh::LeanObject,
    mut v_decl_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2446_, v_decl_2448_);
    return v___x_2449_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_fvar_elim___redArg(
    mut v_t_2450_: *mut crate::leanh::LeanObject,
    mut v_fvar_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2450_, v_fvar_2451_);
    return v___x_2452_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_fvar_elim(
    mut v_motive_2453_: *mut crate::leanh::LeanObject,
    mut v_t_2454_: *mut crate::leanh::LeanObject,
    mut v_h_2455_: *mut crate::leanh::LeanObject,
    mut v_fvar_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2454_, v_fvar_2456_);
    return v___x_2457_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_stx_elim___redArg(
    mut v_t_2458_: *mut crate::leanh::LeanObject,
    mut v_stx_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2458_, v_stx_2459_);
    return v___x_2460_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_stx_elim(
    mut v_motive_2461_: *mut crate::leanh::LeanObject,
    mut v_t_2462_: *mut crate::leanh::LeanObject,
    mut v_h_2463_: *mut crate::leanh::LeanObject,
    mut v_stx_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2462_, v_stx_2464_);
    return v___x_2465_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_local_elim___redArg(
    mut v_t_2466_: *mut crate::leanh::LeanObject,
    mut v_local_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2466_, v_local_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_local_elim(
    mut v_motive_2469_: *mut crate::leanh::LeanObject,
    mut v_t_2470_: *mut crate::leanh::LeanObject,
    mut v_h_2471_: *mut crate::leanh::LeanObject,
    mut v_local_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_2470_, v_local_2472_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2485_ = lean_nat_to_int(v___x_2484_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2487_ = lean_nat_to_int(v___x_2486_);
    return v___x_2487_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprOrigin_repr(
    mut v_x_2506_: *mut crate::leanh::LeanObject,
    mut v_prec_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___y_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_id_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2506_) {
                0 => {
                    v_declName_2508_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    crate::leanh::lean_inc(v_declName_2508_);
                    crate::leanh::lean_dec_ref_known(v_x_2506_, 1);
                    v___x_2519_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2520_ = lean_nat_dec_le(v___x_2519_, v_prec_2507_);
                    if v___x_2520_ == 0 {
                        v___x_2521_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3,
                        );
                        v___y_2510_ = v___x_2521_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2522_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4,
                        );
                        v___y_2510_ = v___x_2522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_fvarId_2523_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    crate::leanh::lean_inc(v_fvarId_2523_);
                    crate::leanh::lean_dec_ref_known(v_x_2506_, 1);
                    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2535_ = lean_nat_dec_le(v___x_2534_, v_prec_2507_);
                    if v___x_2535_ == 0 {
                        v___x_2536_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3,
                        );
                        v___y_2525_ = v___x_2536_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2537_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4,
                        );
                        v___y_2525_ = v___x_2537_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_id_2538_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    v_ref_2539_ = crate::leanh::lean_ctor_get(v_x_2506_, 1);
                    v_isSharedCheck_2563_ = (!crate::leanh::lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2563_ == 0 {
                        v___x_2541_ = v_x_2506_;
                        v_isShared_2542_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ref_2539_);
                        crate::leanh::lean_inc(v_id_2538_);
                        crate::leanh::lean_dec(v_x_2506_);
                        v___x_2541_ = crate::leanh::lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_id_2564_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    crate::leanh::lean_inc(v_id_2564_);
                    crate::leanh::lean_dec_ref_known(v_x_2506_, 1);
                    v___x_2575_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2576_ = lean_nat_dec_le(v___x_2575_, v_prec_2507_);
                    if v___x_2576_ == 0 {
                        v___x_2577_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3,
                        );
                        v___y_2566_ = v___x_2577_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2578_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4,
                        );
                        v___y_2566_ = v___x_2578_;
                        state = 6;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2511_ = l_Lean_Meta_Grind_instReprOrigin_repr___closed__2;
                v___x_2512_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2513_ = l_Lean_Name_reprPrec(v_declName_2508_, v___x_2512_);
                v___x_2514_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2511_);
                crate::leanh::lean_ctor_set(v___x_2514_, 1, v___x_2513_);
                crate::leanh::lean_inc(v___y_2510_);
                v___x_2515_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2515_, 0, v___y_2510_);
                crate::leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
                v___x_2516_ = 0;
                v___x_2517_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2515_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2517_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2516_,
                );
                v___x_2518_ = l_Repr_addAppParen(v___x_2517_, v_prec_2507_);
                return v___x_2518_;
            }
            2 => {
                v___x_2526_ = l_Lean_Meta_Grind_instReprOrigin_repr___closed__7;
                v___x_2527_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2528_ = l_Lean_Name_reprPrec(v_fvarId_2523_, v___x_2527_);
                v___x_2529_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2526_);
                crate::leanh::lean_ctor_set(v___x_2529_, 1, v___x_2528_);
                crate::leanh::lean_inc(v___y_2525_);
                v___x_2530_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2530_, 0, v___y_2525_);
                crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                v___x_2531_ = 0;
                v___x_2532_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2530_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2532_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2531_,
                );
                v___x_2533_ = l_Repr_addAppParen(v___x_2532_, v_prec_2507_);
                return v___x_2533_;
            }
            3 => {
                v___x_2559_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2560_ = lean_nat_dec_le(v___x_2559_, v_prec_2507_);
                if v___x_2560_ == 0 {
                    v___x_2561_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3,
                    );
                    v___y_2544_ = v___x_2561_;
                    state = 4;
                    continue;
                } else {
                    v___x_2562_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instReprOrigin_repr___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4,
                    );
                    v___y_2544_ = v___x_2562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2545_ = crate::leanh::lean_box(1);
                v___x_2546_ = l_Lean_Meta_Grind_instReprOrigin_repr___closed__10;
                v___x_2547_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2548_ = l_Lean_Name_reprPrec(v_id_2538_, v___x_2547_);
                if v_isShared_2542_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2541_, 5);
                    crate::leanh::lean_ctor_set(v___x_2541_, 1, v___x_2548_);
                    crate::leanh::lean_ctor_set(v___x_2541_, 0, v___x_2546_);
                    v___x_2550_ = v___x_2541_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2548_);
                    v___x_2550_ = v_reuseFailAlloc_2558_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2551_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
                crate::leanh::lean_ctor_set(v___x_2551_, 1, v___x_2545_);
                v___x_2552_ = l_Lean_Syntax_instRepr_repr(v_ref_2539_, v___x_2547_);
                v___x_2553_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2553_, 0, v___x_2551_);
                crate::leanh::lean_ctor_set(v___x_2553_, 1, v___x_2552_);
                crate::leanh::lean_inc(v___y_2544_);
                v___x_2554_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2554_, 0, v___y_2544_);
                crate::leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                v___x_2555_ = 0;
                v___x_2556_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2554_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2556_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2555_,
                );
                v___x_2557_ = l_Repr_addAppParen(v___x_2556_, v_prec_2507_);
                return v___x_2557_;
            }
            6 => {
                v___x_2567_ = l_Lean_Meta_Grind_instReprOrigin_repr___closed__13;
                v___x_2568_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_2569_ = l_Lean_Name_reprPrec(v_id_2564_, v___x_2568_);
                v___x_2570_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2567_);
                crate::leanh::lean_ctor_set(v___x_2570_, 1, v___x_2569_);
                crate::leanh::lean_inc(v___y_2566_);
                v___x_2571_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2571_, 0, v___y_2566_);
                crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2570_);
                v___x_2572_ = 0;
                v___x_2573_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2573_, 0, v___x_2571_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2572_,
                );
                v___x_2574_ = l_Repr_addAppParen(v___x_2573_, v_prec_2507_);
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instReprOrigin_repr___boxed(
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_prec_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Lean_Meta_Grind_instReprOrigin_repr(v_x_2579_, v_prec_2580_);
    crate::leanh::lean_dec(v_prec_2580_);
    return v_res_2581_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_key(
    mut v_x_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_declName_2585_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
    crate::leanh::lean_inc(v_declName_2585_);
    return v_declName_2585_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_key___boxed(
    mut v_x_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lean_Meta_Grind_Origin_key(v_x_2586_);
    crate::leanh::lean_dec_ref(v_x_2586_);
    return v_res_2587_;
}
pub unsafe fn l_Lean_Meta_Grind_Origin_pp(
    mut v_o_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_o_2588_) {
        0 => {
            let mut v_declName_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2590_: u8 = 0;
            let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_declName_2589_ = crate::leanh::lean_ctor_get(v_o_2588_, 0);
            crate::leanh::lean_inc(v_declName_2589_);
            crate::leanh::lean_dec_ref_known(v_o_2588_, 1);
            v___x_2590_ = 0;
            v___x_2591_ = l_Lean_MessageData_ofConstName(v_declName_2589_, v___x_2590_);
            return v___x_2591_;
        }
        1 => {
            let mut v_fvarId_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_2592_ = crate::leanh::lean_ctor_get(v_o_2588_, 0);
            crate::leanh::lean_inc(v_fvarId_2592_);
            crate::leanh::lean_dec_ref_known(v_o_2588_, 1);
            v___x_2593_ = l_Lean_mkFVar(v_fvarId_2592_);
            v___x_2594_ = l_Lean_MessageData_ofExpr(v___x_2593_);
            return v___x_2594_;
        }
        2 => {
            let mut v_ref_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ref_2595_ = crate::leanh::lean_ctor_get(v_o_2588_, 1);
            crate::leanh::lean_inc(v_ref_2595_);
            crate::leanh::lean_dec_ref_known(v_o_2588_, 2);
            v___x_2596_ = l_Lean_MessageData_ofSyntax(v_ref_2595_);
            return v___x_2596_;
        }
        _ => {
            let mut v_id_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_id_2597_ = crate::leanh::lean_ctor_get(v_o_2588_, 0);
            crate::leanh::lean_inc(v_id_2597_);
            crate::leanh::lean_dec_ref_known(v_o_2588_, 1);
            v___x_2598_ = l_Lean_MessageData_ofName(v_id_2597_);
            return v___x_2598_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instBEqOrigin___lam__0(
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_b_2600_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v_declName_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2605_ = crate::leanh::lean_ctor_get(v_a_2599_, 0);
                v___y_2602_ = v_declName_2605_;
                state = 1;
                continue;
            }
            1 => {
                v_declName_2603_ = crate::leanh::lean_ctor_get(v_b_2600_, 0);
                v___x_2604_ = lean_name_eq(v___y_2602_, v_declName_2603_);
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_b_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2608_: u8 = 0;
    let mut v_r_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2608_ = l_Lean_Meta_Grind_instBEqOrigin___lam__0(v_a_2606_, v_b_2607_);
    crate::leanh::lean_dec_ref(v_b_2607_);
    crate::leanh::lean_dec_ref(v_a_2606_);
    v_r_2609_ = crate::leanh::lean_box((v_res_2608_) as usize);
    return v_r_2609_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0() -> u64 {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: u64 = 0;
    v___x_2612_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2613_ = lean_uint64_of_nat(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn l_Lean_Meta_Grind_instHashableOrigin___lam__0(
    mut v_a_2614_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___y_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: u64 = 0;
    let mut v_hash_2618_: u64 = 0;
    let mut v_declName_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2619_ = crate::leanh::lean_ctor_get(v_a_2614_, 0);
                v___y_2616_ = v_declName_2619_;
                state = 1;
                continue;
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2616_) == 0 {
                    v___x_2617_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    return v___x_2617_;
                } else {
                    v_hash_2618_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_2616_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    return v_hash_2618_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(
    mut v_a_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2621_: u64 = 0;
    let mut v_r_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2621_ = l_Lean_Meta_Grind_instHashableOrigin___lam__0(v_a_2620_);
    crate::leanh::lean_dec_ref(v_a_2620_);
    v_r_2622_ = crate::leanh::lean_box_uint64(v_res_2621_);
    return v_r_2622_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2625_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
    v___x_2627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2627_, 0, v___x_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(
    mut v_00_u03b2_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1);
    return v___x_2629_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2630_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0,
    );
    v___x_2632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
    return v___x_2632_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2633_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(crate::leanh::lean_box(0));
    return v___x_2633_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2,
    );
    v___x_2635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1,
    );
    v___x_2636_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2635_);
    crate::leanh::lean_ctor_set(v___x_2636_, 1, v___x_2634_);
    crate::leanh::lean_ctor_set(v___x_2636_, 2, v___x_2634_);
    crate::leanh::lean_ctor_set(v___x_2636_, 3, v___x_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Meta_Grind_instInhabitedTheorems_default(
    mut v_00_u03b1_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3,
    );
    return v___x_2638_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(crate::leanh::lean_box(0));
    return v___x_2639_;
}
pub unsafe fn l_Lean_Meta_Grind_instInhabitedTheorems(
    mut v_a_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0,
    );
    return v___x_2641_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0,
    );
    v___x_2662_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9;
    v___x_2663_ = l_instInhabitedOfMonad___redArg(v___x_2662_, v___x_2661_);
    return v___x_2663_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13;
    v___x_2668_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_2669_ = crate::leanh::lean_unsigned_to_nat(82);
    v___x_2670_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12;
    v___x_2671_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11;
    v___x_2672_ = l_mkPanicMessageWithDecl(
        v___x_2671_,
        v___x_2670_,
        v___x_2669_,
        v___x_2668_,
        v___x_2667_,
    );
    return v___x_2672_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_insert___redArg(
    mut v_inst_2675_: *mut crate::leanh::LeanObject,
    mut v_s_2676_: *mut crate::leanh::LeanObject,
    mut v_thm_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getSymbols_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setSymbols_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOrigin_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2690_: u8 = 0;
    let mut v_constName_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_smap_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2698_: u8 = 0;
    let mut v___f_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_isSharedCheck_2735_: u8 = 0;
    let mut v_unused_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getSymbols_2678_ = crate::leanh::lean_ctor_get(v_inst_2675_, 0);
                crate::leanh::lean_inc_ref(v_getSymbols_2678_);
                v_setSymbols_2679_ = crate::leanh::lean_ctor_get(v_inst_2675_, 1);
                crate::leanh::lean_inc(v_setSymbols_2679_);
                v_getOrigin_2680_ = crate::leanh::lean_ctor_get(v_inst_2675_, 2);
                crate::leanh::lean_inc_ref(v_getOrigin_2680_);
                crate::leanh::lean_dec_ref(v_inst_2675_);
                v___x_2681_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once
                    ),
                    _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10,
                );
                crate::leanh::lean_inc(v_thm_2677_);
                v___x_2685_ = crate::leanh::lean_apply_1(v_getSymbols_2678_, v_thm_2677_);
                if crate::leanh::lean_obj_tag(v___x_2685_) == 1 {
                    v_head_2686_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                    crate::leanh::lean_inc(v_head_2686_);
                    if crate::leanh::lean_obj_tag(v_head_2686_) == 2 {
                        v_tail_2687_ = crate::leanh::lean_ctor_get(v___x_2685_, 1);
                        v_isSharedCheck_2735_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2685_)) as u8;
                        if v_isSharedCheck_2735_ == 0 {
                            v_unused_2736_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                            crate::leanh::lean_dec(v_unused_2736_);
                            v___x_2689_ = v___x_2685_;
                            v_isShared_2690_ = v_isSharedCheck_2735_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_2687_);
                            crate::leanh::lean_dec(v___x_2685_);
                            v___x_2689_ = crate::leanh::lean_box(0);
                            v_isShared_2690_ = v_isSharedCheck_2735_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_head_2686_);
                        crate::leanh::lean_dec_ref_known(v___x_2685_, 2);
                        crate::leanh::lean_dec_ref(v_getOrigin_2680_);
                        crate::leanh::lean_dec(v_setSymbols_2679_);
                        crate::leanh::lean_dec(v_thm_2677_);
                        crate::leanh::lean_dec_ref(v_s_2676_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2685_);
                    crate::leanh::lean_dec_ref(v_getOrigin_2680_);
                    crate::leanh::lean_dec(v_setSymbols_2679_);
                    crate::leanh::lean_dec(v_thm_2677_);
                    crate::leanh::lean_dec_ref(v_s_2676_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2683_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once
                    ),
                    _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14,
                );
                v___x_2684_ = l_panic___redArg(v___x_2681_, v___x_2683_);
                return v___x_2684_;
            }
            2 => {
                v_constName_2691_ = crate::leanh::lean_ctor_get(v_head_2686_, 0);
                crate::leanh::lean_inc(v_constName_2691_);
                crate::leanh::lean_dec_ref_known(v_head_2686_, 1);
                v_smap_2692_ = crate::leanh::lean_ctor_get(v_s_2676_, 0);
                v_origins_2693_ = crate::leanh::lean_ctor_get(v_s_2676_, 1);
                v_erased_2694_ = crate::leanh::lean_ctor_get(v_s_2676_, 2);
                v_omap_2695_ = crate::leanh::lean_ctor_get(v_s_2676_, 3);
                v_isSharedCheck_2734_ = (!crate::leanh::lean_is_exclusive(v_s_2676_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v___x_2697_ = v_s_2676_;
                    v_isShared_2698_ = v_isSharedCheck_2734_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_omap_2695_);
                    crate::leanh::lean_inc(v_erased_2694_);
                    crate::leanh::lean_inc(v_origins_2693_);
                    crate::leanh::lean_inc(v_smap_2692_);
                    crate::leanh::lean_dec(v_s_2676_);
                    v___x_2697_ = crate::leanh::lean_box(0);
                    v_isShared_2698_ = v_isSharedCheck_2734_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_2699_ = l_Lean_Meta_Grind_instBEqOrigin___closed__0;
                v___f_2700_ = l_Lean_Meta_Grind_instHashableOrigin___closed__0;
                v___x_2701_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15;
                v___x_2702_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16;
                v_thm_2703_ =
                    crate::leanh::lean_apply_2(v_setSymbols_2679_, v_thm_2677_, v_tail_2687_);
                crate::leanh::lean_inc(v_thm_2703_);
                v_origin_2704_ = crate::leanh::lean_apply_1(v_getOrigin_2680_, v_thm_2703_);
                v___x_2705_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref_n(v_origin_2704_, 2);
                v_origins_2706_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_2699_,
                    v___f_2700_,
                    v_origins_2693_,
                    v_origin_2704_,
                    v___x_2705_,
                );
                v_erased_2707_ = l_Lean_PersistentHashMap_erase___redArg(
                    v___f_2699_,
                    v___f_2700_,
                    v_erased_2694_,
                    v_origin_2704_,
                );
                crate::leanh::lean_inc(v_constName_2691_);
                v___x_2727_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_2701_,
                    v___x_2702_,
                    v_smap_2692_,
                    v_constName_2691_,
                );
                if crate::leanh::lean_obj_tag(v___x_2727_) == 1 {
                    v_val_2728_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                    crate::leanh::lean_inc(v_val_2728_);
                    crate::leanh::lean_dec_ref_known(v___x_2727_, 1);
                    crate::leanh::lean_inc(v_thm_2703_);
                    v___x_2729_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2729_, 0, v_thm_2703_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 1, v_val_2728_);
                    v___x_2730_ = l_Lean_PersistentHashMap_insert___redArg(
                        v___x_2701_,
                        v___x_2702_,
                        v_smap_2692_,
                        v_constName_2691_,
                        v___x_2729_,
                    );
                    v___y_2709_ = v___x_2730_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2727_);
                    v___x_2731_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_thm_2703_);
                    v___x_2732_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2732_, 0, v_thm_2703_);
                    crate::leanh::lean_ctor_set(v___x_2732_, 1, v___x_2731_);
                    v___x_2733_ = l_Lean_PersistentHashMap_insert___redArg(
                        v___x_2701_,
                        v___x_2702_,
                        v_smap_2692_,
                        v_constName_2691_,
                        v___x_2732_,
                    );
                    v___y_2709_ = v___x_2733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_origin_2704_);
                v___x_2710_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___f_2699_,
                    v___f_2700_,
                    v_omap_2695_,
                    v_origin_2704_,
                );
                if crate::leanh::lean_obj_tag(v___x_2710_) == 1 {
                    v_val_2711_ = crate::leanh::lean_ctor_get(v___x_2710_, 0);
                    crate::leanh::lean_inc(v_val_2711_);
                    crate::leanh::lean_dec_ref_known(v___x_2710_, 1);
                    if v_isShared_2690_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2689_, 1, v_val_2711_);
                        crate::leanh::lean_ctor_set(v___x_2689_, 0, v_thm_2703_);
                        v___x_2713_ = v___x_2689_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_thm_2703_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_val_2711_);
                        v___x_2713_ = v_reuseFailAlloc_2718_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2710_);
                    v___x_2719_ = crate::leanh::lean_box(0);
                    if v_isShared_2690_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2689_, 1, v___x_2719_);
                        crate::leanh::lean_ctor_set(v___x_2689_, 0, v_thm_2703_);
                        v___x_2721_ = v___x_2689_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2726_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_thm_2703_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2719_);
                        v___x_2721_ = v_reuseFailAlloc_2726_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2714_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_2699_,
                    v___f_2700_,
                    v_omap_2695_,
                    v_origin_2704_,
                    v___x_2713_,
                );
                if v_isShared_2698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2697_, 3, v___x_2714_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 2, v_erased_2707_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 1, v_origins_2706_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 0, v___y_2709_);
                    v___x_2716_ = v___x_2697_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2717_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___y_2709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_origins_2706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_erased_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 3, v___x_2714_);
                    v___x_2716_ = v_reuseFailAlloc_2717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2716_;
            }
            7 => {
                v___x_2722_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_2699_,
                    v___f_2700_,
                    v_omap_2695_,
                    v_origin_2704_,
                    v___x_2721_,
                );
                if v_isShared_2698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2697_, 3, v___x_2722_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 2, v_erased_2707_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 1, v_origins_2706_);
                    crate::leanh::lean_ctor_set(v___x_2697_, 0, v___y_2709_);
                    v___x_2724_ = v___x_2697_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___y_2709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_origins_2706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_erased_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 3, v___x_2722_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_insert(
    mut v_00_u03b1_2737_: *mut crate::leanh::LeanObject,
    mut v_inst_2738_: *mut crate::leanh::LeanObject,
    mut v_s_2739_: *mut crate::leanh::LeanObject,
    mut v_thm_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2738_, v_s_2739_, v_thm_2740_);
    return v___x_2741_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2742_: *mut crate::leanh::LeanObject,
    mut v_i_2743_: *mut crate::leanh::LeanObject,
    mut v_k_2744_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    let mut v_k_x27_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2752_ = lean_array_get_size(v_keys_2742_);
                v___x_2753_ = lean_nat_dec_lt(v_i_2743_, v___x_2752_);
                if v___x_2753_ == 0 {
                    crate::leanh::lean_dec(v_i_2743_);
                    return v___x_2753_;
                } else {
                    v_k_x27_2754_ = lean_array_fget_borrowed(v_keys_2742_, v_i_2743_);
                    v_declName_2758_ = crate::leanh::lean_ctor_get(v_k_2744_, 0);
                    v___y_2756_ = v_declName_2758_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2748_ = lean_name_eq(v___y_2746_, v___y_2747_);
                if v___x_2748_ == 0 {
                    v___x_2749_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2750_ = lean_nat_add(v_i_2743_, v___x_2749_);
                    crate::leanh::lean_dec(v_i_2743_);
                    v_i_2743_ = v___x_2750_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_i_2743_);
                    return v___x_2748_;
                }
            }
            2 => {
                v_declName_2757_ = crate::leanh::lean_ctor_get(v_k_x27_2754_, 0);
                v___y_2746_ = v___y_2756_;
                v___y_2747_ = v_declName_2757_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2759_: *mut crate::leanh::LeanObject,
    mut v_i_2760_: *mut crate::leanh::LeanObject,
    mut v_k_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2762_: u8 = 0;
    let mut v_r_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2762_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_2759_, v_i_2760_, v_k_2761_);
    crate::leanh::lean_dec_ref(v_k_2761_);
    crate::leanh::lean_dec_ref(v_keys_2759_);
    v_r_2763_ = crate::leanh::lean_box((v_res_2762_) as usize);
    return v_r_2763_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2766_: usize = 0;
    v___x_2764_ = 5usize;
    v___x_2765_ = 1usize;
    v___x_2766_ = lean_usize_shift_left(v___x_2765_, v___x_2764_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2767_: usize = 0;
    let mut v___x_2768_: usize = 0;
    let mut v___x_2769_: usize = 0;
    v___x_2767_ = 1usize;
    v___x_2768_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0);
    v___x_2769_ = lean_usize_sub(v___x_2768_, v___x_2767_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(
    mut v_x_2770_: *mut crate::leanh::LeanObject,
    mut v_x_2771_: usize,
    mut v_x_2772_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: usize = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: usize = 0;
    let mut v_j_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: u8 = 0;
    let mut v_declName_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: usize = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v_ks_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2770_) == 0 {
                    v_es_2773_ = crate::leanh::lean_ctor_get(v_x_2770_, 0);
                    v___x_2774_ = crate::leanh::lean_box(2);
                    v___x_2775_ = 5usize;
                    v___x_2776_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2777_ = lean_usize_land(v_x_2771_, v___x_2776_);
                    v_j_2778_ = lean_usize_to_nat(v___x_2777_);
                    v___x_2779_ = lean_array_get_borrowed(v___x_2774_, v_es_2773_, v_j_2778_);
                    crate::leanh::lean_dec(v_j_2778_);
                    match crate::leanh::lean_obj_tag(v___x_2779_) {
                        0 => {
                            v_key_2780_ = crate::leanh::lean_ctor_get(v___x_2779_, 0);
                            v_declName_2785_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
                            v___y_2782_ = v_declName_2785_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_2786_ = crate::leanh::lean_ctor_get(v___x_2779_, 0);
                            v___x_2787_ = lean_usize_shift_right(v_x_2771_, v___x_2775_);
                            v_x_2770_ = v_node_2786_;
                            v_x_2771_ = v___x_2787_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2789_ = 0;
                            return v___x_2789_;
                        }
                    }
                } else {
                    v_ks_2790_ = crate::leanh::lean_ctor_get(v_x_2770_, 0);
                    v___x_2791_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_ks_2790_, v___x_2791_, v_x_2772_);
                    return v___x_2792_;
                }
            }
            1 => {
                v_declName_2783_ = crate::leanh::lean_ctor_get(v_key_2780_, 0);
                v___x_2784_ = lean_name_eq(v___y_2782_, v_declName_2783_);
                return v___x_2784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(
    mut v_x_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
    mut v_x_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_220__boxed_2796_: usize = 0;
    let mut v_res_2797_: u8 = 0;
    let mut v_r_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_220__boxed_2796_ = crate::leanh::lean_unbox_usize(v_x_2794_);
    crate::leanh::lean_dec(v_x_2794_);
    v_res_2797_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_2793_, v_x_220__boxed_2796_, v_x_2795_);
    crate::leanh::lean_dec_ref(v_x_2795_);
    crate::leanh::lean_dec_ref(v_x_2793_);
    v_r_2798_ = crate::leanh::lean_box((v_res_2797_) as usize);
    return v_r_2798_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(
    mut v_x_2799_: *mut crate::leanh::LeanObject,
    mut v_x_2800_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2802_: u64 = 0;
    let mut v___x_2803_: usize = 0;
    let mut v___x_2804_: u8 = 0;
    let mut v___y_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u64 = 0;
    let mut v_hash_2808_: u64 = 0;
    let mut v_declName_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2809_ = crate::leanh::lean_ctor_get(v_x_2800_, 0);
                v___y_2806_ = v_declName_2809_;
                state = 2;
                continue;
            }
            1 => {
                v___x_2803_ = lean_uint64_to_usize(v___y_2802_);
                v___x_2804_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_2799_, v___x_2803_, v_x_2800_);
                return v___x_2804_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2806_) == 0 {
                    v___x_2807_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    v___y_2802_ = v___x_2807_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2808_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_2806_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2802_ = v_hash_2808_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(
    mut v_x_2810_: *mut crate::leanh::LeanObject,
    mut v_x_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2812_: u8 = 0;
    let mut v_r_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_2810_, v_x_2811_);
    crate::leanh::lean_dec_ref(v_x_2811_);
    crate::leanh::lean_dec_ref(v_x_2810_);
    v_r_2813_ = crate::leanh::lean_box((v_res_2812_) as usize);
    return v_r_2813_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_contains___redArg(
    mut v_s_2814_: *mut crate::leanh::LeanObject,
    mut v_origin_2815_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_origins_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    v_origins_2816_ = crate::leanh::lean_ctor_get(v_s_2814_, 1);
    v___x_2817_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_origins_2816_, v_origin_2815_);
    return v___x_2817_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(
    mut v_s_2818_: *mut crate::leanh::LeanObject,
    mut v_origin_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2820_: u8 = 0;
    let mut v_r_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_2818_, v_origin_2819_);
    crate::leanh::lean_dec_ref(v_origin_2819_);
    crate::leanh::lean_dec_ref(v_s_2818_);
    v_r_2821_ = crate::leanh::lean_box((v_res_2820_) as usize);
    return v_r_2821_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_contains(
    mut v_00_u03b1_2822_: *mut crate::leanh::LeanObject,
    mut v_s_2823_: *mut crate::leanh::LeanObject,
    mut v_origin_2824_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2825_: u8 = 0;
    v___x_2825_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_2823_, v_origin_2824_);
    return v___x_2825_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_contains___boxed(
    mut v_00_u03b1_2826_: *mut crate::leanh::LeanObject,
    mut v_s_2827_: *mut crate::leanh::LeanObject,
    mut v_origin_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2829_: u8 = 0;
    let mut v_r_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_Meta_Grind_Theorems_contains(v_00_u03b1_2826_, v_s_2827_, v_origin_2828_);
    crate::leanh::lean_dec_ref(v_origin_2828_);
    crate::leanh::lean_dec_ref(v_s_2827_);
    v_r_2830_ = crate::leanh::lean_box((v_res_2829_) as usize);
    return v_r_2830_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(
    mut v_00_u03b2_2831_: *mut crate::leanh::LeanObject,
    mut v_x_2832_: *mut crate::leanh::LeanObject,
    mut v_x_2833_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2834_: u8 = 0;
    v___x_2834_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_2832_, v_x_2833_);
    return v___x_2834_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(
    mut v_00_u03b2_2835_: *mut crate::leanh::LeanObject,
    mut v_x_2836_: *mut crate::leanh::LeanObject,
    mut v_x_2837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2838_: u8 = 0;
    let mut v_r_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2838_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(
            v_00_u03b2_2835_,
            v_x_2836_,
            v_x_2837_,
        );
    crate::leanh::lean_dec_ref(v_x_2837_);
    crate::leanh::lean_dec_ref(v_x_2836_);
    v_r_2839_ = crate::leanh::lean_box((v_res_2838_) as usize);
    return v_r_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(
    mut v_00_u03b2_2840_: *mut crate::leanh::LeanObject,
    mut v_x_2841_: *mut crate::leanh::LeanObject,
    mut v_x_2842_: usize,
    mut v_x_2843_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2844_: u8 = 0;
    v___x_2844_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_2841_, v_x_2842_, v_x_2843_);
    return v___x_2844_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(
    mut v_00_u03b2_2845_: *mut crate::leanh::LeanObject,
    mut v_x_2846_: *mut crate::leanh::LeanObject,
    mut v_x_2847_: *mut crate::leanh::LeanObject,
    mut v_x_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_327__boxed_2849_: usize = 0;
    let mut v_res_2850_: u8 = 0;
    let mut v_r_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_327__boxed_2849_ = crate::leanh::lean_unbox_usize(v_x_2847_);
    crate::leanh::lean_dec(v_x_2847_);
    v_res_2850_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(v_00_u03b2_2845_, v_x_2846_, v_x_327__boxed_2849_, v_x_2848_);
    crate::leanh::lean_dec_ref(v_x_2848_);
    crate::leanh::lean_dec_ref(v_x_2846_);
    v_r_2851_ = crate::leanh::lean_box((v_res_2850_) as usize);
    return v_r_2851_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2852_: *mut crate::leanh::LeanObject,
    mut v_keys_2853_: *mut crate::leanh::LeanObject,
    mut v_vals_2854_: *mut crate::leanh::LeanObject,
    mut v_heq_2855_: *mut crate::leanh::LeanObject,
    mut v_i_2856_: *mut crate::leanh::LeanObject,
    mut v_k_2857_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2858_: u8 = 0;
    v___x_2858_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_2853_, v_i_2856_, v_k_2857_);
    return v___x_2858_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2859_: *mut crate::leanh::LeanObject,
    mut v_keys_2860_: *mut crate::leanh::LeanObject,
    mut v_vals_2861_: *mut crate::leanh::LeanObject,
    mut v_heq_2862_: *mut crate::leanh::LeanObject,
    mut v_i_2863_: *mut crate::leanh::LeanObject,
    mut v_k_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2865_: u8 = 0;
    let mut v_r_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(v_00_u03b2_2859_, v_keys_2860_, v_vals_2861_, v_heq_2862_, v_i_2863_, v_k_2864_);
    crate::leanh::lean_dec_ref(v_k_2864_);
    crate::leanh::lean_dec_ref(v_vals_2861_);
    crate::leanh::lean_dec_ref(v_keys_2860_);
    v_r_2866_ = crate::leanh::lean_box((v_res_2865_) as usize);
    return v_r_2866_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(
    mut v_xs_2867_: *mut crate::leanh::LeanObject,
    mut v_v_2868_: *mut crate::leanh::LeanObject,
    mut v_i_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2881_ = lean_array_get_size(v_xs_2867_);
                v___x_2882_ = lean_nat_dec_lt(v_i_2869_, v___x_2881_);
                if v___x_2882_ == 0 {
                    crate::leanh::lean_dec(v_i_2869_);
                    v___x_2883_ = crate::leanh::lean_box(0);
                    return v___x_2883_;
                } else {
                    v___x_2884_ = lean_array_fget_borrowed(v_xs_2867_, v_i_2869_);
                    v_declName_2885_ = crate::leanh::lean_ctor_get(v___x_2884_, 0);
                    v___y_2879_ = v_declName_2885_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2873_ = lean_name_eq(v___y_2871_, v___y_2872_);
                if v___x_2873_ == 0 {
                    v___x_2874_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2875_ = lean_nat_add(v_i_2869_, v___x_2874_);
                    crate::leanh::lean_dec(v_i_2869_);
                    v_i_2869_ = v___x_2875_;
                    state = 0;
                    continue;
                } else {
                    v___x_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2877_, 0, v_i_2869_);
                    return v___x_2877_;
                }
            }
            2 => {
                v_declName_2880_ = crate::leanh::lean_ctor_get(v_v_2868_, 0);
                v___y_2871_ = v___y_2879_;
                v___y_2872_ = v_declName_2880_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_xs_2886_: *mut crate::leanh::LeanObject,
    mut v_v_2887_: *mut crate::leanh::LeanObject,
    mut v_i_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2886_, v_v_2887_, v_i_2888_);
    crate::leanh::lean_dec_ref(v_v_2887_);
    crate::leanh::lean_dec_ref(v_xs_2886_);
    return v_res_2889_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(
    mut v_xs_2890_: *mut crate::leanh::LeanObject,
    mut v_v_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2892_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2893_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2890_, v_v_2891_, v___x_2892_);
    return v___x_2893_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2894_: *mut crate::leanh::LeanObject,
    mut v_v_2895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2896_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_xs_2894_, v_v_2895_);
    crate::leanh::lean_dec_ref(v_v_2895_);
    crate::leanh::lean_dec_ref(v_xs_2894_);
    return v_res_2896_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(
    mut v_x_2897_: *mut crate::leanh::LeanObject,
    mut v_x_2898_: usize,
    mut v_x_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: usize = 0;
    let mut v___x_2903_: usize = 0;
    let mut v___x_2904_: usize = 0;
    let mut v_j_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_unused_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v_node_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_entries_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: usize = 0;
    let mut v_newNode_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_unused_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2897_) == 0 {
                    v_es_2900_ = crate::leanh::lean_ctor_get(v_x_2897_, 0);
                    v___x_2901_ = crate::leanh::lean_box(2);
                    v___x_2902_ = 5usize;
                    v___x_2903_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2904_ = lean_usize_land(v_x_2898_, v___x_2903_);
                    v_j_2905_ = lean_usize_to_nat(v___x_2904_);
                    v_entry_2919_ = lean_array_get(v___x_2901_, v_es_2900_, v_j_2905_);
                    match crate::leanh::lean_obj_tag(v_entry_2919_) {
                        0 => {
                            v_key_2920_ = crate::leanh::lean_ctor_get(v_entry_2919_, 0);
                            crate::leanh::lean_inc(v_key_2920_);
                            crate::leanh::lean_dec_ref_known(v_entry_2919_, 2);
                            v_declName_2924_ = crate::leanh::lean_ctor_get(v_x_2899_, 0);
                            v___y_2922_ = v_declName_2924_;
                            state = 4;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc_ref(v_es_2900_);
                            v_isSharedCheck_2958_ =
                                (!crate::leanh::lean_is_exclusive(v_x_2897_)) as u8;
                            if v_isSharedCheck_2958_ == 0 {
                                v_unused_2959_ = crate::leanh::lean_ctor_get(v_x_2897_, 0);
                                crate::leanh::lean_dec(v_unused_2959_);
                                v___x_2926_ = v_x_2897_;
                                v_isShared_2927_ = v_isSharedCheck_2958_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_2897_);
                                v___x_2926_ = crate::leanh::lean_box(0);
                                v_isShared_2927_ = v_isSharedCheck_2958_;
                                state = 5;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_j_2905_);
                            return v_x_2897_;
                        }
                    }
                } else {
                    v_ks_2960_ = crate::leanh::lean_ctor_get(v_x_2897_, 0);
                    v_vs_2961_ = crate::leanh::lean_ctor_get(v_x_2897_, 1);
                    v_isSharedCheck_2975_ = (!crate::leanh::lean_is_exclusive(v_x_2897_)) as u8;
                    if v_isSharedCheck_2975_ == 0 {
                        v___x_2963_ = v_x_2897_;
                        v_isShared_2964_ = v_isSharedCheck_2975_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2961_);
                        crate::leanh::lean_inc(v_ks_2960_);
                        crate::leanh::lean_dec(v_x_2897_);
                        v___x_2963_ = crate::leanh::lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2975_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2909_ = lean_name_eq(v___y_2907_, v___y_2908_);
                crate::leanh::lean_dec(v___y_2908_);
                if v___x_2909_ == 0 {
                    crate::leanh::lean_dec(v_j_2905_);
                    return v_x_2897_;
                } else {
                    crate::leanh::lean_inc_ref(v_es_2900_);
                    v_isSharedCheck_2917_ = (!crate::leanh::lean_is_exclusive(v_x_2897_)) as u8;
                    if v_isSharedCheck_2917_ == 0 {
                        v_unused_2918_ = crate::leanh::lean_ctor_get(v_x_2897_, 0);
                        crate::leanh::lean_dec(v_unused_2918_);
                        v___x_2911_ = v_x_2897_;
                        v_isShared_2912_ = v_isSharedCheck_2917_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2897_);
                        v___x_2911_ = crate::leanh::lean_box(0);
                        v_isShared_2912_ = v_isSharedCheck_2917_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2913_ = lean_array_set(v_es_2900_, v_j_2905_, v___x_2901_);
                crate::leanh::lean_dec(v_j_2905_);
                if v_isShared_2912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2911_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
                    v___x_2915_ = v_reuseFailAlloc_2916_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2915_;
            }
            4 => {
                v_declName_2923_ = crate::leanh::lean_ctor_get(v_key_2920_, 0);
                crate::leanh::lean_inc(v_declName_2923_);
                crate::leanh::lean_dec(v_key_2920_);
                v___y_2907_ = v___y_2922_;
                v___y_2908_ = v_declName_2923_;
                state = 1;
                continue;
            }
            5 => {
                v_node_2928_ = crate::leanh::lean_ctor_get(v_entry_2919_, 0);
                v_isSharedCheck_2957_ = (!crate::leanh::lean_is_exclusive(v_entry_2919_)) as u8;
                if v_isSharedCheck_2957_ == 0 {
                    v___x_2930_ = v_entry_2919_;
                    v_isShared_2931_ = v_isSharedCheck_2957_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_node_2928_);
                    crate::leanh::lean_dec(v_entry_2919_);
                    v___x_2930_ = crate::leanh::lean_box(0);
                    v_isShared_2931_ = v_isSharedCheck_2957_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_entries_2932_ = lean_array_set(v_es_2900_, v_j_2905_, v___x_2901_);
                v___x_2933_ = lean_usize_shift_right(v_x_2898_, v___x_2902_);
                v_newNode_2934_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_node_2928_, v___x_2933_, v_x_2899_);
                crate::leanh::lean_inc_ref(v_newNode_2934_);
                v___x_2935_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2934_);
                if crate::leanh::lean_obj_tag(v___x_2935_) == 0 {
                    if v_isShared_2931_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2930_, 0, v_newNode_2934_);
                        v___x_2937_ = v___x_2930_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_newNode_2934_);
                        v___x_2937_ = v_reuseFailAlloc_2942_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_newNode_2934_);
                    crate::leanh::lean_del_object(v___x_2930_);
                    v_val_2943_ = crate::leanh::lean_ctor_get(v___x_2935_, 0);
                    crate::leanh::lean_inc(v_val_2943_);
                    crate::leanh::lean_dec_ref_known(v___x_2935_, 1);
                    v_fst_2944_ = crate::leanh::lean_ctor_get(v_val_2943_, 0);
                    v_snd_2945_ = crate::leanh::lean_ctor_get(v_val_2943_, 1);
                    v_isSharedCheck_2956_ = (!crate::leanh::lean_is_exclusive(v_val_2943_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2947_ = v_val_2943_;
                        v_isShared_2948_ = v_isSharedCheck_2956_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2945_);
                        crate::leanh::lean_inc(v_fst_2944_);
                        crate::leanh::lean_dec(v_val_2943_);
                        v___x_2947_ = crate::leanh::lean_box(0);
                        v_isShared_2948_ = v_isSharedCheck_2956_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2938_ = lean_array_set(v_entries_2932_, v_j_2905_, v___x_2937_);
                crate::leanh::lean_dec(v_j_2905_);
                if v_isShared_2927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2926_, 0, v___x_2938_);
                    v___x_2940_ = v___x_2926_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2940_;
            }
            9 => {
                if v_isShared_2948_ == 0 {
                    v___x_2950_ = v___x_2947_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_fst_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_snd_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2955_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2951_ = lean_array_set(v_entries_2932_, v_j_2905_, v___x_2950_);
                crate::leanh::lean_dec(v_j_2905_);
                if v_isShared_2927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2926_, 0, v___x_2951_);
                    v___x_2953_ = v___x_2926_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2953_;
            }
            12 => {
                v___x_2965_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_ks_2960_, v_x_2899_);
                if crate::leanh::lean_obj_tag(v___x_2965_) == 0 {
                    if v_isShared_2964_ == 0 {
                        v___x_2967_ = v___x_2963_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2968_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_ks_2960_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_vs_2961_);
                        v___x_2967_ = v_reuseFailAlloc_2968_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_val_2969_ = crate::leanh::lean_ctor_get(v___x_2965_, 0);
                    crate::leanh::lean_inc_n(v_val_2969_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2965_, 1);
                    v_keys_x27_2970_ = l_Array_eraseIdx___redArg(v_ks_2960_, v_val_2969_);
                    v_vals_x27_2971_ = l_Array_eraseIdx___redArg(v_vs_2961_, v_val_2969_);
                    if v_isShared_2964_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2963_, 1, v_vals_x27_2971_);
                        crate::leanh::lean_ctor_set(v___x_2963_, 0, v_keys_x27_2970_);
                        v___x_2973_ = v___x_2963_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2974_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_keys_x27_2970_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_vals_x27_2971_);
                        v___x_2973_ = v_reuseFailAlloc_2974_;
                        state = 14;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_2967_;
            }
            14 => {
                return v___x_2973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(
    mut v_x_2976_: *mut crate::leanh::LeanObject,
    mut v_x_2977_: *mut crate::leanh::LeanObject,
    mut v_x_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_606__boxed_2979_: usize = 0;
    let mut v_res_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_606__boxed_2979_ = crate::leanh::lean_unbox_usize(v_x_2977_);
    crate::leanh::lean_dec(v_x_2977_);
    v_res_2980_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_2976_, v_x_606__boxed_2979_, v_x_2978_);
    crate::leanh::lean_dec_ref(v_x_2978_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(
    mut v_x_2981_: *mut crate::leanh::LeanObject,
    mut v_x_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2984_: u64 = 0;
    let mut v_h_2985_: usize = 0;
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u64 = 0;
    let mut v_hash_2990_: u64 = 0;
    let mut v_declName_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2991_ = crate::leanh::lean_ctor_get(v_x_2982_, 0);
                v___y_2988_ = v_declName_2991_;
                state = 2;
                continue;
            }
            1 => {
                v_h_2985_ = lean_uint64_to_usize(v___y_2984_);
                v___x_2986_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_2981_, v_h_2985_, v_x_2982_);
                return v___x_2986_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2988_) == 0 {
                    v___x_2989_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    v___y_2984_ = v___x_2989_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2990_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_2988_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2984_ = v_hash_2990_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(
    mut v_x_2992_: *mut crate::leanh::LeanObject,
    mut v_x_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(
            v_x_2992_, v_x_2993_,
        );
    crate::leanh::lean_dec_ref(v_x_2993_);
    return v_res_2994_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_x_2995_: *mut crate::leanh::LeanObject,
    mut v_x_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
    mut v_x_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v___y_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2999_ = crate::leanh::lean_ctor_get(v_x_2995_, 0);
                v_vs_3000_ = crate::leanh::lean_ctor_get(v_x_2995_, 1);
                v_isSharedCheck_3029_ = (!crate::leanh::lean_is_exclusive(v_x_2995_)) as u8;
                if v_isSharedCheck_3029_ == 0 {
                    v___x_3002_ = v_x_2995_;
                    v_isShared_3003_ = v_isSharedCheck_3029_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3000_);
                    crate::leanh::lean_inc(v_ks_2999_);
                    crate::leanh::lean_dec(v_x_2995_);
                    v___x_3002_ = crate::leanh::lean_box(0);
                    v_isShared_3003_ = v_isSharedCheck_3029_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3019_ = lean_array_get_size(v_ks_2999_);
                v___x_3020_ = lean_nat_dec_lt(v_x_2996_, v___x_3019_);
                if v___x_3020_ == 0 {
                    crate::leanh::lean_del_object(v___x_3002_);
                    crate::leanh::lean_dec(v_x_2996_);
                    v___x_3021_ = lean_array_push(v_ks_2999_, v_x_2997_);
                    v___x_3022_ = lean_array_push(v_vs_3000_, v_x_2998_);
                    v___x_3023_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3023_, 0, v___x_3021_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 1, v___x_3022_);
                    return v___x_3023_;
                } else {
                    v_k_x27_3024_ = lean_array_fget_borrowed(v_ks_2999_, v_x_2996_);
                    v_declName_3028_ = crate::leanh::lean_ctor_get(v_x_2997_, 0);
                    crate::leanh::lean_inc(v_declName_3028_);
                    v___y_3026_ = v_declName_3028_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_3007_ = lean_name_eq(v___y_3005_, v___y_3006_);
                crate::leanh::lean_dec(v___y_3006_);
                crate::leanh::lean_dec(v___y_3005_);
                if v___x_3007_ == 0 {
                    if v_isShared_3003_ == 0 {
                        v___x_3009_ = v___x_3002_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_ks_2999_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_vs_3000_);
                        v___x_3009_ = v_reuseFailAlloc_3013_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3014_ = lean_array_fset(v_ks_2999_, v_x_2996_, v_x_2997_);
                    v___x_3015_ = lean_array_fset(v_vs_3000_, v_x_2996_, v_x_2998_);
                    crate::leanh::lean_dec(v_x_2996_);
                    if v_isShared_3003_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3002_, 1, v___x_3015_);
                        crate::leanh::lean_ctor_set(v___x_3002_, 0, v___x_3014_);
                        v___x_3017_ = v___x_3002_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3014_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3015_);
                        v___x_3017_ = v_reuseFailAlloc_3018_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3010_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3011_ = lean_nat_add(v_x_2996_, v___x_3010_);
                crate::leanh::lean_dec(v_x_2996_);
                v_x_2995_ = v___x_3009_;
                v_x_2996_ = v___x_3011_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3017_;
            }
            5 => {
                v_declName_3027_ = crate::leanh::lean_ctor_get(v_k_x27_3024_, 0);
                crate::leanh::lean_inc(v_declName_3027_);
                v___y_3005_ = v___y_3026_;
                v___y_3006_ = v_declName_3027_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(
    mut v_n_3030_: *mut crate::leanh::LeanObject,
    mut v_k_3031_: *mut crate::leanh::LeanObject,
    mut v_v_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3034_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_n_3030_, v___x_3033_, v_k_3031_, v_v_3032_);
    return v___x_3034_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3035_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(
    mut v_x_3036_: *mut crate::leanh::LeanObject,
    mut v_x_3037_: usize,
    mut v_x_3038_: usize,
    mut v_x_3039_: *mut crate::leanh::LeanObject,
    mut v_x_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    let mut v___x_3045_: usize = 0;
    let mut v_j_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v_v_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___y_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v_node_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: usize = 0;
    let mut v___x_3085_: usize = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_unused_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3103_: u8 = 0;
    let mut v_ks_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: usize = 0;
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v_reuseFailAlloc_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3036_) == 0 {
                    v_es_3041_ = crate::leanh::lean_ctor_get(v_x_3036_, 0);
                    v___x_3042_ = 5usize;
                    v___x_3043_ = 1usize;
                    v___x_3044_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_3045_ = lean_usize_land(v_x_3037_, v___x_3044_);
                    v_j_3046_ = lean_usize_to_nat(v___x_3045_);
                    v___x_3047_ = lean_array_get_size(v_es_3041_);
                    v___x_3048_ = lean_nat_dec_lt(v_j_3046_, v___x_3047_);
                    if v___x_3048_ == 0 {
                        crate::leanh::lean_dec(v_j_3046_);
                        crate::leanh::lean_dec(v_x_3040_);
                        crate::leanh::lean_dec_ref(v_x_3039_);
                        return v_x_3036_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3041_);
                        v_isSharedCheck_3092_ = (!crate::leanh::lean_is_exclusive(v_x_3036_)) as u8;
                        if v_isSharedCheck_3092_ == 0 {
                            v_unused_3093_ = crate::leanh::lean_ctor_get(v_x_3036_, 0);
                            crate::leanh::lean_dec(v_unused_3093_);
                            v___x_3050_ = v_x_3036_;
                            v_isShared_3051_ = v_isSharedCheck_3092_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3036_);
                            v___x_3050_ = crate::leanh::lean_box(0);
                            v_isShared_3051_ = v_isSharedCheck_3092_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3094_ = crate::leanh::lean_ctor_get(v_x_3036_, 0);
                    v_vs_3095_ = crate::leanh::lean_ctor_get(v_x_3036_, 1);
                    v_isSharedCheck_3115_ = (!crate::leanh::lean_is_exclusive(v_x_3036_)) as u8;
                    if v_isSharedCheck_3115_ == 0 {
                        v___x_3097_ = v_x_3036_;
                        v_isShared_3098_ = v_isSharedCheck_3115_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3095_);
                        crate::leanh::lean_inc(v_ks_3094_);
                        crate::leanh::lean_dec(v_x_3036_);
                        v___x_3097_ = crate::leanh::lean_box(0);
                        v_isShared_3098_ = v_isSharedCheck_3115_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3052_ = lean_array_fget(v_es_3041_, v_j_3046_);
                v___x_3053_ = crate::leanh::lean_box(0);
                v_xs_x27_3054_ = lean_array_fset(v_es_3041_, v_j_3046_, v___x_3053_);
                match crate::leanh::lean_obj_tag(v_v_3052_) {
                    0 => {
                        v_key_3061_ = crate::leanh::lean_ctor_get(v_v_3052_, 0);
                        v_val_3062_ = crate::leanh::lean_ctor_get(v_v_3052_, 1);
                        v_isSharedCheck_3079_ = (!crate::leanh::lean_is_exclusive(v_v_3052_)) as u8;
                        if v_isSharedCheck_3079_ == 0 {
                            v___x_3064_ = v_v_3052_;
                            v_isShared_3065_ = v_isSharedCheck_3079_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3062_);
                            crate::leanh::lean_inc(v_key_3061_);
                            crate::leanh::lean_dec(v_v_3052_);
                            v___x_3064_ = crate::leanh::lean_box(0);
                            v_isShared_3065_ = v_isSharedCheck_3079_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3080_ = crate::leanh::lean_ctor_get(v_v_3052_, 0);
                        v_isSharedCheck_3090_ = (!crate::leanh::lean_is_exclusive(v_v_3052_)) as u8;
                        if v_isSharedCheck_3090_ == 0 {
                            v___x_3082_ = v_v_3052_;
                            v_isShared_3083_ = v_isSharedCheck_3090_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3080_);
                            crate::leanh::lean_dec(v_v_3052_);
                            v___x_3082_ = crate::leanh::lean_box(0);
                            v_isShared_3083_ = v_isSharedCheck_3090_;
                            state = 8;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3091_, 0, v_x_3039_);
                        crate::leanh::lean_ctor_set(v___x_3091_, 1, v_x_3040_);
                        v___y_3056_ = v___x_3091_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3057_ = lean_array_fset(v_xs_x27_3054_, v_j_3046_, v___y_3056_);
                crate::leanh::lean_dec(v_j_3046_);
                if v_isShared_3051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3050_, 0, v___x_3057_);
                    v___x_3059_ = v___x_3050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
                    v___x_3059_ = v_reuseFailAlloc_3060_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3059_;
            }
            4 => {
                v_declName_3078_ = crate::leanh::lean_ctor_get(v_x_3039_, 0);
                crate::leanh::lean_inc(v_declName_3078_);
                v___y_3076_ = v_declName_3078_;
                state = 7;
                continue;
            }
            5 => {
                v___x_3069_ = lean_name_eq(v___y_3067_, v___y_3068_);
                crate::leanh::lean_dec(v___y_3068_);
                crate::leanh::lean_dec(v___y_3067_);
                if v___x_3069_ == 0 {
                    crate::leanh::lean_del_object(v___x_3064_);
                    v___x_3070_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3061_,
                        v_val_3062_,
                        v_x_3039_,
                        v_x_3040_,
                    );
                    v___x_3071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3071_, 0, v___x_3070_);
                    v___y_3056_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3062_);
                    crate::leanh::lean_dec(v_key_3061_);
                    if v_isShared_3065_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3064_, 1, v_x_3040_);
                        crate::leanh::lean_ctor_set(v___x_3064_, 0, v_x_3039_);
                        v___x_3073_ = v___x_3064_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_x_3039_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_x_3040_);
                        v___x_3073_ = v_reuseFailAlloc_3074_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___y_3056_ = v___x_3073_;
                state = 2;
                continue;
            }
            7 => {
                v_declName_3077_ = crate::leanh::lean_ctor_get(v_key_3061_, 0);
                crate::leanh::lean_inc(v_declName_3077_);
                v___y_3067_ = v___y_3076_;
                v___y_3068_ = v_declName_3077_;
                state = 5;
                continue;
            }
            8 => {
                v___x_3084_ = lean_usize_shift_right(v_x_3037_, v___x_3042_);
                v___x_3085_ = lean_usize_add(v_x_3038_, v___x_3043_);
                v___x_3086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_node_3080_, v___x_3084_, v___x_3085_, v_x_3039_, v_x_3040_);
                if v_isShared_3083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3086_);
                    v___x_3088_ = v___x_3082_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
                    v___x_3088_ = v_reuseFailAlloc_3089_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_3056_ = v___x_3088_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_3098_ == 0 {
                    v___x_3100_ = v___x_3097_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_ks_3094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_vs_3095_);
                    v___x_3100_ = v_reuseFailAlloc_3114_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_newNode_3101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v___x_3100_, v_x_3039_, v_x_3040_);
                v___x_3109_ = 7usize;
                v___x_3110_ = lean_usize_dec_le(v___x_3109_, v_x_3038_);
                if v___x_3110_ == 0 {
                    v___x_3111_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3101_);
                    v___x_3112_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3113_ = lean_nat_dec_lt(v___x_3111_, v___x_3112_);
                    crate::leanh::lean_dec(v___x_3111_);
                    v___y_3103_ = v___x_3113_;
                    state = 12;
                    continue;
                } else {
                    v___y_3103_ = v___x_3110_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v___y_3103_ == 0 {
                    v_ks_3104_ = crate::leanh::lean_ctor_get(v_newNode_3101_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3104_);
                    v_vs_3105_ = crate::leanh::lean_ctor_get(v_newNode_3101_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3105_);
                    crate::leanh::lean_dec_ref(v_newNode_3101_);
                    v___x_3106_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0);
                    v___x_3108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_x_3038_, v_ks_3104_, v_vs_3105_, v___x_3106_, v___x_3107_);
                    crate::leanh::lean_dec_ref(v_vs_3105_);
                    crate::leanh::lean_dec_ref(v_ks_3104_);
                    return v___x_3108_;
                } else {
                    return v_newNode_3101_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(
    mut v_depth_3116_: usize,
    mut v_keys_3117_: *mut crate::leanh::LeanObject,
    mut v_vals_3118_: *mut crate::leanh::LeanObject,
    mut v_i_3119_: *mut crate::leanh::LeanObject,
    mut v_entries_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v_k_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: u64 = 0;
    let mut v_h_3127_: usize = 0;
    let mut v___x_3128_: usize = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: usize = 0;
    let mut v___x_3131_: usize = 0;
    let mut v___x_3132_: usize = 0;
    let mut v_h_3133_: usize = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u64 = 0;
    let mut v_hash_3140_: u64 = 0;
    let mut v_declName_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3121_ = lean_array_get_size(v_keys_3117_);
                v___x_3122_ = lean_nat_dec_lt(v_i_3119_, v___x_3121_);
                if v___x_3122_ == 0 {
                    crate::leanh::lean_dec(v_i_3119_);
                    return v_entries_3120_;
                } else {
                    v_k_3123_ = lean_array_fget_borrowed(v_keys_3117_, v_i_3119_);
                    v_v_3124_ = lean_array_fget_borrowed(v_vals_3118_, v_i_3119_);
                    v_declName_3141_ = crate::leanh::lean_ctor_get(v_k_3123_, 0);
                    crate::leanh::lean_inc(v_declName_3141_);
                    v___y_3138_ = v_declName_3141_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_h_3127_ = lean_uint64_to_usize(v___y_3126_);
                v___x_3128_ = 5usize;
                v___x_3129_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3130_ = 1usize;
                v___x_3131_ = lean_usize_sub(v_depth_3116_, v___x_3130_);
                v___x_3132_ = lean_usize_mul(v___x_3128_, v___x_3131_);
                v_h_3133_ = lean_usize_shift_right(v_h_3127_, v___x_3132_);
                v___x_3134_ = lean_nat_add(v_i_3119_, v___x_3129_);
                crate::leanh::lean_dec(v_i_3119_);
                crate::leanh::lean_inc(v_v_3124_);
                crate::leanh::lean_inc(v_k_3123_);
                v___x_3135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_entries_3120_, v_h_3133_, v_depth_3116_, v_k_3123_, v_v_3124_);
                v_i_3119_ = v___x_3134_;
                v_entries_3120_ = v___x_3135_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3138_) == 0 {
                    v___x_3139_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    v___y_3126_ = v___x_3139_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3140_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_3138_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___y_3138_);
                    v___y_3126_ = v_hash_3140_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_3142_: *mut crate::leanh::LeanObject,
    mut v_keys_3143_: *mut crate::leanh::LeanObject,
    mut v_vals_3144_: *mut crate::leanh::LeanObject,
    mut v_i_3145_: *mut crate::leanh::LeanObject,
    mut v_entries_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3147_: usize = 0;
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3147_ = crate::leanh::lean_unbox_usize(v_depth_3142_);
    crate::leanh::lean_dec(v_depth_3142_);
    v_res_3148_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3147_, v_keys_3143_, v_vals_3144_, v_i_3145_, v_entries_3146_);
    crate::leanh::lean_dec_ref(v_vals_3144_);
    crate::leanh::lean_dec_ref(v_keys_3143_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(
    mut v_x_3149_: *mut crate::leanh::LeanObject,
    mut v_x_3150_: *mut crate::leanh::LeanObject,
    mut v_x_3151_: *mut crate::leanh::LeanObject,
    mut v_x_3152_: *mut crate::leanh::LeanObject,
    mut v_x_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_905__boxed_3154_: usize = 0;
    let mut v_x_906__boxed_3155_: usize = 0;
    let mut v_res_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_905__boxed_3154_ = crate::leanh::lean_unbox_usize(v_x_3150_);
    crate::leanh::lean_dec(v_x_3150_);
    v_x_906__boxed_3155_ = crate::leanh::lean_unbox_usize(v_x_3151_);
    crate::leanh::lean_dec(v_x_3151_);
    v_res_3156_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_3149_, v_x_905__boxed_3154_, v_x_906__boxed_3155_, v_x_3152_, v_x_3153_);
    return v_res_3156_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(
    mut v_x_3157_: *mut crate::leanh::LeanObject,
    mut v_x_3158_: *mut crate::leanh::LeanObject,
    mut v_x_3159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3161_: u64 = 0;
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u64 = 0;
    let mut v_hash_3168_: u64 = 0;
    let mut v_declName_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_3169_ = crate::leanh::lean_ctor_get(v_x_3158_, 0);
                crate::leanh::lean_inc(v_declName_3169_);
                v___y_3166_ = v_declName_3169_;
                state = 2;
                continue;
            }
            1 => {
                v___x_3162_ = lean_uint64_to_usize(v___y_3161_);
                v___x_3163_ = 1usize;
                v___x_3164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_3157_, v___x_3162_, v___x_3163_, v_x_3158_, v_x_3159_);
                return v___x_3164_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3166_) == 0 {
                    v___x_3167_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    v___y_3161_ = v___x_3167_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3168_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_3166_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___y_3166_);
                    v___y_3161_ = v_hash_3168_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_erase___redArg(
    mut v_s_3170_: *mut crate::leanh::LeanObject,
    mut v_origin_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_smap_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3178_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_smap_3172_ = crate::leanh::lean_ctor_get(v_s_3170_, 0);
                v_origins_3173_ = crate::leanh::lean_ctor_get(v_s_3170_, 1);
                v_erased_3174_ = crate::leanh::lean_ctor_get(v_s_3170_, 2);
                v_omap_3175_ = crate::leanh::lean_ctor_get(v_s_3170_, 3);
                v_isSharedCheck_3185_ = (!crate::leanh::lean_is_exclusive(v_s_3170_)) as u8;
                if v_isSharedCheck_3185_ == 0 {
                    v___x_3177_ = v_s_3170_;
                    v_isShared_3178_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_omap_3175_);
                    crate::leanh::lean_inc(v_erased_3174_);
                    crate::leanh::lean_inc(v_origins_3173_);
                    crate::leanh::lean_inc(v_smap_3172_);
                    crate::leanh::lean_dec(v_s_3170_);
                    v___x_3177_ = crate::leanh::lean_box(0);
                    v_isShared_3178_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3179_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_origins_3173_, v_origin_3171_);
                v___x_3180_ = crate::leanh::lean_box(0);
                v___x_3181_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_erased_3174_, v_origin_3171_, v___x_3180_);
                if v_isShared_3178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3177_, 2, v___x_3181_);
                    crate::leanh::lean_ctor_set(v___x_3177_, 1, v___x_3179_);
                    v___x_3183_ = v___x_3177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_smap_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 2, v___x_3181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_omap_3175_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_erase(
    mut v_00_u03b1_3186_: *mut crate::leanh::LeanObject,
    mut v_s_3187_: *mut crate::leanh::LeanObject,
    mut v_origin_3188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_3187_, v_origin_3188_);
    return v___x_3189_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(
    mut v_00_u03b2_3190_: *mut crate::leanh::LeanObject,
    mut v_x_3191_: *mut crate::leanh::LeanObject,
    mut v_x_3192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(
            v_x_3191_, v_x_3192_,
        );
    return v___x_3193_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(
    mut v_00_u03b2_3194_: *mut crate::leanh::LeanObject,
    mut v_x_3195_: *mut crate::leanh::LeanObject,
    mut v_x_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(
        v_00_u03b2_3194_,
        v_x_3195_,
        v_x_3196_,
    );
    crate::leanh::lean_dec_ref(v_x_3196_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(
    mut v_00_u03b2_3198_: *mut crate::leanh::LeanObject,
    mut v_x_3199_: *mut crate::leanh::LeanObject,
    mut v_x_3200_: *mut crate::leanh::LeanObject,
    mut v_x_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(
            v_x_3199_, v_x_3200_, v_x_3201_,
        );
    return v___x_3202_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(
    mut v_00_u03b2_3203_: *mut crate::leanh::LeanObject,
    mut v_x_3204_: *mut crate::leanh::LeanObject,
    mut v_x_3205_: usize,
    mut v_x_3206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_3204_, v_x_3205_, v_x_3206_);
    return v___x_3207_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(
    mut v_00_u03b2_3208_: *mut crate::leanh::LeanObject,
    mut v_x_3209_: *mut crate::leanh::LeanObject,
    mut v_x_3210_: *mut crate::leanh::LeanObject,
    mut v_x_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1157__boxed_3212_: usize = 0;
    let mut v_res_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1157__boxed_3212_ = crate::leanh::lean_unbox_usize(v_x_3210_);
    crate::leanh::lean_dec(v_x_3210_);
    v_res_3213_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(v_00_u03b2_3208_, v_x_3209_, v_x_1157__boxed_3212_, v_x_3211_);
    crate::leanh::lean_dec_ref(v_x_3211_);
    return v_res_3213_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(
    mut v_00_u03b2_3214_: *mut crate::leanh::LeanObject,
    mut v_x_3215_: *mut crate::leanh::LeanObject,
    mut v_x_3216_: usize,
    mut v_x_3217_: usize,
    mut v_x_3218_: *mut crate::leanh::LeanObject,
    mut v_x_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_3215_, v_x_3216_, v_x_3217_, v_x_3218_, v_x_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(
    mut v_00_u03b2_3221_: *mut crate::leanh::LeanObject,
    mut v_x_3222_: *mut crate::leanh::LeanObject,
    mut v_x_3223_: *mut crate::leanh::LeanObject,
    mut v_x_3224_: *mut crate::leanh::LeanObject,
    mut v_x_3225_: *mut crate::leanh::LeanObject,
    mut v_x_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1168__boxed_3227_: usize = 0;
    let mut v_x_1169__boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1168__boxed_3227_ = crate::leanh::lean_unbox_usize(v_x_3223_);
    crate::leanh::lean_dec(v_x_3223_);
    v_x_1169__boxed_3228_ = crate::leanh::lean_unbox_usize(v_x_3224_);
    crate::leanh::lean_dec(v_x_3224_);
    v_res_3229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(v_00_u03b2_3221_, v_x_3222_, v_x_1168__boxed_3227_, v_x_1169__boxed_3228_, v_x_3225_, v_x_3226_);
    return v_res_3229_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3230_: *mut crate::leanh::LeanObject,
    mut v_n_3231_: *mut crate::leanh::LeanObject,
    mut v_k_3232_: *mut crate::leanh::LeanObject,
    mut v_v_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v_n_3231_, v_k_3232_, v_v_3233_);
    return v___x_3234_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3235_: *mut crate::leanh::LeanObject,
    mut v_depth_3236_: usize,
    mut v_keys_3237_: *mut crate::leanh::LeanObject,
    mut v_vals_3238_: *mut crate::leanh::LeanObject,
    mut v_heq_3239_: *mut crate::leanh::LeanObject,
    mut v_i_3240_: *mut crate::leanh::LeanObject,
    mut v_entries_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_3236_, v_keys_3237_, v_vals_3238_, v_i_3240_, v_entries_3241_);
    return v___x_3242_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_3243_: *mut crate::leanh::LeanObject,
    mut v_depth_3244_: *mut crate::leanh::LeanObject,
    mut v_keys_3245_: *mut crate::leanh::LeanObject,
    mut v_vals_3246_: *mut crate::leanh::LeanObject,
    mut v_heq_3247_: *mut crate::leanh::LeanObject,
    mut v_i_3248_: *mut crate::leanh::LeanObject,
    mut v_entries_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3250_: usize = 0;
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3250_ = crate::leanh::lean_unbox_usize(v_depth_3244_);
    crate::leanh::lean_dec(v_depth_3244_);
    v_res_3251_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(v_00_u03b2_3243_, v_depth_boxed_3250_, v_keys_3245_, v_vals_3246_, v_heq_3247_, v_i_3248_, v_entries_3249_);
    crate::leanh::lean_dec_ref(v_vals_3246_);
    crate::leanh::lean_dec_ref(v_keys_3245_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_3252_: *mut crate::leanh::LeanObject,
    mut v_x_3253_: *mut crate::leanh::LeanObject,
    mut v_x_3254_: *mut crate::leanh::LeanObject,
    mut v_x_3255_: *mut crate::leanh::LeanObject,
    mut v_x_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_x_3253_, v_x_3254_, v_x_3255_, v_x_3256_);
    return v___x_3257_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_isErased___redArg(
    mut v_s_3258_: *mut crate::leanh::LeanObject,
    mut v_origin_3259_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_erased_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    v_erased_3260_ = crate::leanh::lean_ctor_get(v_s_3258_, 2);
    v___x_3261_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_3260_, v_origin_3259_);
    return v___x_3261_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(
    mut v_s_3262_: *mut crate::leanh::LeanObject,
    mut v_origin_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3264_: u8 = 0;
    let mut v_r_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_3262_, v_origin_3263_);
    crate::leanh::lean_dec_ref(v_origin_3263_);
    crate::leanh::lean_dec_ref(v_s_3262_);
    v_r_3265_ = crate::leanh::lean_box((v_res_3264_) as usize);
    return v_r_3265_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_isErased(
    mut v_00_u03b1_3266_: *mut crate::leanh::LeanObject,
    mut v_s_3267_: *mut crate::leanh::LeanObject,
    mut v_origin_3268_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3269_: u8 = 0;
    v___x_3269_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_3267_, v_origin_3268_);
    return v___x_3269_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_isErased___boxed(
    mut v_00_u03b1_3270_: *mut crate::leanh::LeanObject,
    mut v_s_3271_: *mut crate::leanh::LeanObject,
    mut v_origin_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3273_: u8 = 0;
    let mut v_r_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3273_ = l_Lean_Meta_Grind_Theorems_isErased(v_00_u03b1_3270_, v_s_3271_, v_origin_3272_);
    crate::leanh::lean_dec_ref(v_origin_3272_);
    crate::leanh::lean_dec_ref(v_s_3271_);
    v_r_3274_ = crate::leanh::lean_box((v_res_3273_) as usize);
    return v_r_3274_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(
    mut v_s_3275_: *mut crate::leanh::LeanObject,
    mut v_sym_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_smap_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3299_: u8 = 0;
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_smap_3277_ = crate::leanh::lean_ctor_get(v_s_3275_, 0);
                v_origins_3278_ = crate::leanh::lean_ctor_get(v_s_3275_, 1);
                v_erased_3279_ = crate::leanh::lean_ctor_get(v_s_3275_, 2);
                v_omap_3280_ = crate::leanh::lean_ctor_get(v_s_3275_, 3);
                v_isSharedCheck_3301_ = (!crate::leanh::lean_is_exclusive(v_s_3275_)) as u8;
                if v_isSharedCheck_3301_ == 0 {
                    v___x_3282_ = v_s_3275_;
                    v_isShared_3283_ = v_isSharedCheck_3301_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_omap_3280_);
                    crate::leanh::lean_inc(v_erased_3279_);
                    crate::leanh::lean_inc(v_origins_3278_);
                    crate::leanh::lean_inc(v_smap_3277_);
                    crate::leanh::lean_dec(v_s_3275_);
                    v___x_3282_ = crate::leanh::lean_box(0);
                    v_isShared_3283_ = v_isSharedCheck_3301_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3284_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15;
                v___x_3285_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16;
                crate::leanh::lean_inc(v_sym_3276_);
                v___x_3286_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_3284_,
                    v___x_3285_,
                    v_smap_3277_,
                    v_sym_3276_,
                );
                if crate::leanh::lean_obj_tag(v___x_3286_) == 1 {
                    v_val_3287_ = crate::leanh::lean_ctor_get(v___x_3286_, 0);
                    v_isSharedCheck_3299_ = (!crate::leanh::lean_is_exclusive(v___x_3286_)) as u8;
                    if v_isSharedCheck_3299_ == 0 {
                        v___x_3289_ = v___x_3286_;
                        v_isShared_3290_ = v_isSharedCheck_3299_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3287_);
                        crate::leanh::lean_dec(v___x_3286_);
                        v___x_3289_ = crate::leanh::lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3299_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3286_);
                    crate::leanh::lean_del_object(v___x_3282_);
                    crate::leanh::lean_dec_ref(v_omap_3280_);
                    crate::leanh::lean_dec_ref(v_erased_3279_);
                    crate::leanh::lean_dec_ref(v_origins_3278_);
                    crate::leanh::lean_dec_ref(v_smap_3277_);
                    crate::leanh::lean_dec(v_sym_3276_);
                    v___x_3300_ = crate::leanh::lean_box(0);
                    return v___x_3300_;
                }
            }
            2 => {
                v___x_3291_ = l_Lean_PersistentHashMap_erase___redArg(
                    v___x_3284_,
                    v___x_3285_,
                    v_smap_3277_,
                    v_sym_3276_,
                );
                if v_isShared_3283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3291_);
                    v___x_3293_ = v___x_3282_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3298_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_origins_3278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_erased_3279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_omap_3280_);
                    v___x_3293_ = v_reuseFailAlloc_3298_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3294_, 0, v_val_3287_);
                crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                if v_isShared_3290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3289_, 0, v___x_3294_);
                    v___x_3296_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
                    v___x_3296_ = v_reuseFailAlloc_3297_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_retrieve_x3f(
    mut v_00_u03b1_3302_: *mut crate::leanh::LeanObject,
    mut v_s_3303_: *mut crate::leanh::LeanObject,
    mut v_sym_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_smap_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3318_: u8 = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_smap_3305_ = crate::leanh::lean_ctor_get(v_s_3303_, 0);
                v_origins_3306_ = crate::leanh::lean_ctor_get(v_s_3303_, 1);
                v_erased_3307_ = crate::leanh::lean_ctor_get(v_s_3303_, 2);
                v_omap_3308_ = crate::leanh::lean_ctor_get(v_s_3303_, 3);
                v_isSharedCheck_3329_ = (!crate::leanh::lean_is_exclusive(v_s_3303_)) as u8;
                if v_isSharedCheck_3329_ == 0 {
                    v___x_3310_ = v_s_3303_;
                    v_isShared_3311_ = v_isSharedCheck_3329_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_omap_3308_);
                    crate::leanh::lean_inc(v_erased_3307_);
                    crate::leanh::lean_inc(v_origins_3306_);
                    crate::leanh::lean_inc(v_smap_3305_);
                    crate::leanh::lean_dec(v_s_3303_);
                    v___x_3310_ = crate::leanh::lean_box(0);
                    v_isShared_3311_ = v_isSharedCheck_3329_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3312_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15;
                v___x_3313_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16;
                crate::leanh::lean_inc(v_sym_3304_);
                v___x_3314_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_3312_,
                    v___x_3313_,
                    v_smap_3305_,
                    v_sym_3304_,
                );
                if crate::leanh::lean_obj_tag(v___x_3314_) == 1 {
                    v_val_3315_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                    v_isSharedCheck_3327_ = (!crate::leanh::lean_is_exclusive(v___x_3314_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v___x_3317_ = v___x_3314_;
                        v_isShared_3318_ = v_isSharedCheck_3327_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3315_);
                        crate::leanh::lean_dec(v___x_3314_);
                        v___x_3317_ = crate::leanh::lean_box(0);
                        v_isShared_3318_ = v_isSharedCheck_3327_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3314_);
                    crate::leanh::lean_del_object(v___x_3310_);
                    crate::leanh::lean_dec_ref(v_omap_3308_);
                    crate::leanh::lean_dec_ref(v_erased_3307_);
                    crate::leanh::lean_dec_ref(v_origins_3306_);
                    crate::leanh::lean_dec_ref(v_smap_3305_);
                    crate::leanh::lean_dec(v_sym_3304_);
                    v___x_3328_ = crate::leanh::lean_box(0);
                    return v___x_3328_;
                }
            }
            2 => {
                v___x_3319_ = l_Lean_PersistentHashMap_erase___redArg(
                    v___x_3312_,
                    v___x_3313_,
                    v_smap_3305_,
                    v_sym_3304_,
                );
                if v_isShared_3311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3310_, 0, v___x_3319_);
                    v___x_3321_ = v___x_3310_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_origins_3306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_erased_3307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 3, v_omap_3308_);
                    v___x_3321_ = v_reuseFailAlloc_3326_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3322_, 0, v_val_3315_);
                crate::leanh::lean_ctor_set(v___x_3322_, 1, v___x_3321_);
                if v_isShared_3318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3317_, 0, v___x_3322_);
                    v___x_3324_ = v___x_3317_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
                    v___x_3324_ = v_reuseFailAlloc_3325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3330_: *mut crate::leanh::LeanObject,
    mut v_vals_3331_: *mut crate::leanh::LeanObject,
    mut v_i_3332_: *mut crate::leanh::LeanObject,
    mut v_k_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3343_ = lean_array_get_size(v_keys_3330_);
                v___x_3344_ = lean_nat_dec_lt(v_i_3332_, v___x_3343_);
                if v___x_3344_ == 0 {
                    crate::leanh::lean_dec(v_i_3332_);
                    v___x_3345_ = crate::leanh::lean_box(0);
                    return v___x_3345_;
                } else {
                    v_k_x27_3346_ = lean_array_fget_borrowed(v_keys_3330_, v_i_3332_);
                    v_declName_3350_ = crate::leanh::lean_ctor_get(v_k_3333_, 0);
                    v___y_3348_ = v_declName_3350_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3337_ = lean_name_eq(v___y_3335_, v___y_3336_);
                if v___x_3337_ == 0 {
                    v___x_3338_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3339_ = lean_nat_add(v_i_3332_, v___x_3338_);
                    crate::leanh::lean_dec(v_i_3332_);
                    v_i_3332_ = v___x_3339_;
                    state = 0;
                    continue;
                } else {
                    v___x_3341_ = lean_array_fget_borrowed(v_vals_3331_, v_i_3332_);
                    crate::leanh::lean_dec(v_i_3332_);
                    crate::leanh::lean_inc(v___x_3341_);
                    v___x_3342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
                    return v___x_3342_;
                }
            }
            2 => {
                v_declName_3349_ = crate::leanh::lean_ctor_get(v_k_x27_3346_, 0);
                v___y_3335_ = v___y_3348_;
                v___y_3336_ = v_declName_3349_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3351_: *mut crate::leanh::LeanObject,
    mut v_vals_3352_: *mut crate::leanh::LeanObject,
    mut v_i_3353_: *mut crate::leanh::LeanObject,
    mut v_k_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_3351_, v_vals_3352_, v_i_3353_, v_k_3354_);
    crate::leanh::lean_dec_ref(v_k_3354_);
    crate::leanh::lean_dec_ref(v_vals_3352_);
    crate::leanh::lean_dec_ref(v_keys_3351_);
    return v_res_3355_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(
    mut v_x_3356_: *mut crate::leanh::LeanObject,
    mut v_x_3357_: usize,
    mut v_x_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: usize = 0;
    let mut v___x_3362_: usize = 0;
    let mut v___x_3363_: usize = 0;
    let mut v_j_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: usize = 0;
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3356_) == 0 {
                    v_es_3359_ = crate::leanh::lean_ctor_get(v_x_3356_, 0);
                    v___x_3360_ = crate::leanh::lean_box(2);
                    v___x_3361_ = 5usize;
                    v___x_3362_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_3363_ = lean_usize_land(v_x_3357_, v___x_3362_);
                    v_j_3364_ = lean_usize_to_nat(v___x_3363_);
                    v___x_3365_ = lean_array_get_borrowed(v___x_3360_, v_es_3359_, v_j_3364_);
                    crate::leanh::lean_dec(v_j_3364_);
                    match crate::leanh::lean_obj_tag(v___x_3365_) {
                        0 => {
                            v_key_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                            v_val_3367_ = crate::leanh::lean_ctor_get(v___x_3365_, 1);
                            v_declName_3377_ = crate::leanh::lean_ctor_get(v_x_3358_, 0);
                            v___y_3375_ = v_declName_3377_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3378_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                            v___x_3379_ = lean_usize_shift_right(v_x_3357_, v___x_3361_);
                            v_x_3356_ = v_node_3378_;
                            v_x_3357_ = v___x_3379_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3381_ = crate::leanh::lean_box(0);
                            return v___x_3381_;
                        }
                    }
                } else {
                    v_ks_3382_ = crate::leanh::lean_ctor_get(v_x_3356_, 0);
                    v_vs_3383_ = crate::leanh::lean_ctor_get(v_x_3356_, 1);
                    v___x_3384_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3385_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_ks_3382_, v_vs_3383_, v___x_3384_, v_x_3358_);
                    return v___x_3385_;
                }
            }
            1 => {
                v___x_3371_ = lean_name_eq(v___y_3369_, v___y_3370_);
                if v___x_3371_ == 0 {
                    v___x_3372_ = crate::leanh::lean_box(0);
                    return v___x_3372_;
                } else {
                    crate::leanh::lean_inc(v_val_3367_);
                    v___x_3373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v_val_3367_);
                    return v___x_3373_;
                }
            }
            2 => {
                v_declName_3376_ = crate::leanh::lean_ctor_get(v_key_3366_, 0);
                v___y_3369_ = v___y_3375_;
                v___y_3370_ = v_declName_3376_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(
    mut v_x_3386_: *mut crate::leanh::LeanObject,
    mut v_x_3387_: *mut crate::leanh::LeanObject,
    mut v_x_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_238__boxed_3389_: usize = 0;
    let mut v_res_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_238__boxed_3389_ = crate::leanh::lean_unbox_usize(v_x_3387_);
    crate::leanh::lean_dec(v_x_3387_);
    v_res_3390_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_3386_, v_x_238__boxed_3389_, v_x_3388_);
    crate::leanh::lean_dec_ref(v_x_3388_);
    crate::leanh::lean_dec_ref(v_x_3386_);
    return v_res_3390_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(
    mut v_x_3391_: *mut crate::leanh::LeanObject,
    mut v_x_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3394_: u64 = 0;
    let mut v___x_3395_: usize = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u64 = 0;
    let mut v_hash_3400_: u64 = 0;
    let mut v_declName_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_3401_ = crate::leanh::lean_ctor_get(v_x_3392_, 0);
                v___y_3398_ = v_declName_3401_;
                state = 2;
                continue;
            }
            1 => {
                v___x_3395_ = lean_uint64_to_usize(v___y_3394_);
                v___x_3396_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_3391_, v___x_3395_, v_x_3392_);
                return v___x_3396_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3398_) == 0 {
                    v___x_3399_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0,
                    );
                    v___y_3394_ = v___x_3399_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3400_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_3398_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3394_ = v_hash_3400_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(
    mut v_x_3402_: *mut crate::leanh::LeanObject,
    mut v_x_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3404_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(
            v_x_3402_, v_x_3403_,
        );
    crate::leanh::lean_dec_ref(v_x_3403_);
    crate::leanh::lean_dec_ref(v_x_3402_);
    return v_res_3404_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_find___redArg(
    mut v_s_3405_: *mut crate::leanh::LeanObject,
    mut v_origin_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_omap_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_omap_3407_ = crate::leanh::lean_ctor_get(v_s_3405_, 3);
    v___x_3408_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(
            v_omap_3407_,
            v_origin_3406_,
        );
    if crate::leanh::lean_obj_tag(v___x_3408_) == 1 {
        let mut v_val_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3409_ = crate::leanh::lean_ctor_get(v___x_3408_, 0);
        crate::leanh::lean_inc(v_val_3409_);
        crate::leanh::lean_dec_ref_known(v___x_3408_, 1);
        return v_val_3409_;
    } else {
        let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3408_);
        v___x_3410_ = crate::leanh::lean_box(0);
        return v___x_3410_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_find___redArg___boxed(
    mut v_s_3411_: *mut crate::leanh::LeanObject,
    mut v_origin_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_3411_, v_origin_3412_);
    crate::leanh::lean_dec_ref(v_origin_3412_);
    crate::leanh::lean_dec_ref(v_s_3411_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_find(
    mut v_00_u03b1_3414_: *mut crate::leanh::LeanObject,
    mut v_s_3415_: *mut crate::leanh::LeanObject,
    mut v_origin_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_3415_, v_origin_3416_);
    return v___x_3417_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_find___boxed(
    mut v_00_u03b1_3418_: *mut crate::leanh::LeanObject,
    mut v_s_3419_: *mut crate::leanh::LeanObject,
    mut v_origin_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Lean_Meta_Grind_Theorems_find(v_00_u03b1_3418_, v_s_3419_, v_origin_3420_);
    crate::leanh::lean_dec_ref(v_origin_3420_);
    crate::leanh::lean_dec_ref(v_s_3419_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(
    mut v_00_u03b2_3422_: *mut crate::leanh::LeanObject,
    mut v_x_3423_: *mut crate::leanh::LeanObject,
    mut v_x_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(
            v_x_3423_, v_x_3424_,
        );
    return v___x_3425_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(
    mut v_00_u03b2_3426_: *mut crate::leanh::LeanObject,
    mut v_x_3427_: *mut crate::leanh::LeanObject,
    mut v_x_3428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3429_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(
        v_00_u03b2_3426_,
        v_x_3427_,
        v_x_3428_,
    );
    crate::leanh::lean_dec_ref(v_x_3428_);
    crate::leanh::lean_dec_ref(v_x_3427_);
    return v_res_3429_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(
    mut v_00_u03b2_3430_: *mut crate::leanh::LeanObject,
    mut v_x_3431_: *mut crate::leanh::LeanObject,
    mut v_x_3432_: usize,
    mut v_x_3433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_3431_, v_x_3432_, v_x_3433_);
    return v___x_3434_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(
    mut v_00_u03b2_3435_: *mut crate::leanh::LeanObject,
    mut v_x_3436_: *mut crate::leanh::LeanObject,
    mut v_x_3437_: *mut crate::leanh::LeanObject,
    mut v_x_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_354__boxed_3439_: usize = 0;
    let mut v_res_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_354__boxed_3439_ = crate::leanh::lean_unbox_usize(v_x_3437_);
    crate::leanh::lean_dec(v_x_3437_);
    v_res_3440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(v_00_u03b2_3435_, v_x_3436_, v_x_354__boxed_3439_, v_x_3438_);
    crate::leanh::lean_dec_ref(v_x_3438_);
    crate::leanh::lean_dec_ref(v_x_3436_);
    return v_res_3440_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3441_: *mut crate::leanh::LeanObject,
    mut v_keys_3442_: *mut crate::leanh::LeanObject,
    mut v_vals_3443_: *mut crate::leanh::LeanObject,
    mut v_heq_3444_: *mut crate::leanh::LeanObject,
    mut v_i_3445_: *mut crate::leanh::LeanObject,
    mut v_k_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_3442_, v_vals_3443_, v_i_3445_, v_k_3446_);
    return v___x_3447_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3448_: *mut crate::leanh::LeanObject,
    mut v_keys_3449_: *mut crate::leanh::LeanObject,
    mut v_vals_3450_: *mut crate::leanh::LeanObject,
    mut v_heq_3451_: *mut crate::leanh::LeanObject,
    mut v_i_3452_: *mut crate::leanh::LeanObject,
    mut v_k_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(v_00_u03b2_3448_, v_keys_3449_, v_vals_3450_, v_heq_3451_, v_i_3452_, v_k_3453_);
    crate::leanh::lean_dec_ref(v_k_3453_);
    crate::leanh::lean_dec_ref(v_vals_3450_);
    crate::leanh::lean_dec_ref(v_keys_3449_);
    return v_res_3454_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(
    mut v_x_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
    return v___x_3461_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(
    mut v_x_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
    mut v___y_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(
        v_x_3462_,
        v___y_3463_,
        v___y_3464_,
        v___y_3465_,
        v___y_3466_,
    );
    crate::leanh::lean_dec(v___y_3466_);
    crate::leanh::lean_dec_ref(v___y_3465_);
    crate::leanh::lean_dec(v___y_3464_);
    crate::leanh::lean_dec_ref(v___y_3463_);
    crate::leanh::lean_dec(v_x_3462_);
    return v_res_3468_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3470_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1,
    );
    v___x_3472_ = l_StateRefT_x27_instMonad___redArg(v___x_3471_);
    return v___x_3472_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3477_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_3478_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3478_, 0, v___x_3477_);
    return v___f_3478_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_3480_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3480_, 0, v___x_3479_);
    return v___f_3480_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3481_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8,
    );
    v___f_3482_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7,
    );
    v___x_3483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3483_, 0, v___f_3482_);
    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___f_3481_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9,
    );
    v___f_3485_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3485_, 0, v___x_3484_);
    return v___f_3485_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9,
    );
    v___f_3487_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3487_, 0, v___x_3486_);
    return v___f_3487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3488_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11,
    );
    v___f_3489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10,
    );
    v___x_3490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3490_, 0, v___f_3489_);
    crate::leanh::lean_ctor_set(v___x_3490_, 1, v___f_3488_);
    return v___x_3490_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_3496_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16;
    v___x_3497_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15;
    v___x_3498_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_3497_,
        v___x_3496_,
        v___x_3495_,
    );
    return v___x_3498_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once
        ),
        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17,
    );
    v___f_3500_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14;
    v___f_3501_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13;
    v___x_3502_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_3501_,
        v___f_3500_,
        v___x_3499_,
    );
    return v___x_3502_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(
    mut v_inst_3503_: *mut crate::leanh::LeanObject,
    mut v_thm_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getProof_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevelParams_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___f_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: u8 = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v_toFunctor_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v___f_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3564_: usize = 0;
    let mut v___x_3565_: usize = 0;
    let mut v___x_898__overap_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3576_: u8 = 0;
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_reuseFailAlloc_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_unused_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_toFunctor_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3621_: u8 = 0;
    let mut v___f_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886__overap_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v_levelParams_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: u8 = 0;
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v_a_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_unused_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_unused_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_unused_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getProof_3510_ = crate::leanh::lean_ctor_get(v_inst_3503_, 3);
                v_getLevelParams_3511_ = crate::leanh::lean_ctor_get(v_inst_3503_, 4);
                v_isSharedCheck_3674_ = (!crate::leanh::lean_is_exclusive(v_inst_3503_)) as u8;
                if v_isSharedCheck_3674_ == 0 {
                    v_unused_3675_ = crate::leanh::lean_ctor_get(v_inst_3503_, 2);
                    crate::leanh::lean_dec(v_unused_3675_);
                    v_unused_3676_ = crate::leanh::lean_ctor_get(v_inst_3503_, 1);
                    crate::leanh::lean_dec(v_unused_3676_);
                    v_unused_3677_ = crate::leanh::lean_ctor_get(v_inst_3503_, 0);
                    crate::leanh::lean_dec(v_unused_3677_);
                    v___x_3513_ = v_inst_3503_;
                    v_isShared_3514_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_getLevelParams_3511_);
                    crate::leanh::lean_inc(v_getProof_3510_);
                    crate::leanh::lean_dec(v_inst_3503_);
                    v___x_3513_ = crate::leanh::lean_box(0);
                    v_isShared_3514_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3515_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0;
                crate::leanh::lean_inc(v_thm_3504_);
                v_proof_3516_ = crate::leanh::lean_apply_1(v_getProof_3510_, v_thm_3504_);
                v_us_3517_ = crate::leanh::lean_apply_1(v_getLevelParams_3511_, v_thm_3504_);
                v___x_3670_ = l_Lean_Expr_isConst(v_proof_3516_);
                if v___x_3670_ == 0 {
                    v___y_3519_ = v___x_3670_;
                    state = 2;
                    continue;
                } else {
                    v___x_3671_ = lean_array_get_size(v_us_3517_);
                    v___x_3672_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
                    v___y_3519_ = v___x_3673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_3519_ == 0 {
                    v___x_3520_ = lean_array_get_size(v_us_3517_);
                    v___x_3521_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3522_ = lean_nat_dec_eq(v___x_3520_, v___x_3521_);
                    if v___x_3522_ == 0 {
                        v___x_3523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once), _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2);
                        v_toApplicative_3524_ = crate::leanh::lean_ctor_get(v___x_3523_, 0);
                        v_toFunctor_3525_ = crate::leanh::lean_ctor_get(v_toApplicative_3524_, 0);
                        v_toSeq_3526_ = crate::leanh::lean_ctor_get(v_toApplicative_3524_, 2);
                        v_toSeqLeft_3527_ = crate::leanh::lean_ctor_get(v_toApplicative_3524_, 3);
                        v_toSeqRight_3528_ = crate::leanh::lean_ctor_get(v_toApplicative_3524_, 4);
                        v___f_3529_ =
                            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3;
                        v___f_3530_ =
                            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4;
                        crate::leanh::lean_inc_ref_n(v_toFunctor_3525_, 2);
                        v___f_3531_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instFunctorOfMonad___redArg___lam__0
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3531_, 0, v_toFunctor_3525_);
                        v___f_3532_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instFunctorOfMonad___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3532_, 0, v_toFunctor_3525_);
                        v___x_3533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3533_, 0, v___f_3531_);
                        crate::leanh::lean_ctor_set(v___x_3533_, 1, v___f_3532_);
                        crate::leanh::lean_inc(v_toSeqRight_3528_);
                        v___f_3534_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3534_, 0, v_toSeqRight_3528_);
                        crate::leanh::lean_inc(v_toSeqLeft_3527_);
                        v___f_3535_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__3
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3535_, 0, v_toSeqLeft_3527_);
                        crate::leanh::lean_inc(v_toSeq_3526_);
                        v___f_3536_ = crate::leanh::lean_alloc_closure(
                            l_ReaderT_instApplicativeOfMonad___redArg___lam__4
                                as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_3536_, 0, v_toSeq_3526_);
                        if v_isShared_3514_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3513_, 4, v___f_3534_);
                            crate::leanh::lean_ctor_set(v___x_3513_, 3, v___f_3535_);
                            crate::leanh::lean_ctor_set(v___x_3513_, 2, v___f_3536_);
                            crate::leanh::lean_ctor_set(v___x_3513_, 1, v___f_3529_);
                            crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3533_);
                            v___x_3538_ = v___x_3513_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3591_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3533_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___f_3529_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 2, v___f_3536_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 3, v___f_3535_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 4, v___f_3534_);
                            v___x_3538_ = v_reuseFailAlloc_3591_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_us_3517_);
                        crate::leanh::lean_del_object(v___x_3513_);
                        v___x_3592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3592_, 0, v_proof_3516_);
                        return v___x_3592_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_us_3517_);
                    v___x_3593_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once
                        ),
                        _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2,
                    );
                    v_toApplicative_3594_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                    v_toFunctor_3595_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 0);
                    v_toSeq_3596_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 2);
                    v_toSeqLeft_3597_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 3);
                    v_toSeqRight_3598_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 4);
                    v___f_3599_ =
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3;
                    v___f_3600_ =
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4;
                    crate::leanh::lean_inc_ref_n(v_toFunctor_3595_, 2);
                    v___f_3601_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3601_, 0, v_toFunctor_3595_);
                    v___f_3602_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3602_, 0, v_toFunctor_3595_);
                    v___x_3603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3603_, 0, v___f_3601_);
                    crate::leanh::lean_ctor_set(v___x_3603_, 1, v___f_3602_);
                    crate::leanh::lean_inc(v_toSeqRight_3598_);
                    v___f_3604_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__1
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3604_, 0, v_toSeqRight_3598_);
                    crate::leanh::lean_inc(v_toSeqLeft_3597_);
                    v___f_3605_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__3
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3605_, 0, v_toSeqLeft_3597_);
                    crate::leanh::lean_inc(v_toSeq_3596_);
                    v___f_3606_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__4
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3606_, 0, v_toSeq_3596_);
                    if v_isShared_3514_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3513_, 4, v___f_3604_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 3, v___f_3605_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 2, v___f_3606_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 1, v___f_3599_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3603_);
                        v___x_3608_ = v___x_3513_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3669_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3603_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___f_3599_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 2, v___f_3606_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 3, v___f_3605_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 4, v___f_3604_);
                        v___x_3608_ = v_reuseFailAlloc_3669_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3539_, 0, v___x_3538_);
                crate::leanh::lean_ctor_set(v___x_3539_, 1, v___f_3530_);
                v___x_3540_ = l_StateRefT_x27_instMonad___redArg(v___x_3539_);
                v_toApplicative_3541_ = crate::leanh::lean_ctor_get(v___x_3540_, 0);
                v_isSharedCheck_3589_ = (!crate::leanh::lean_is_exclusive(v___x_3540_)) as u8;
                if v_isSharedCheck_3589_ == 0 {
                    v_unused_3590_ = crate::leanh::lean_ctor_get(v___x_3540_, 1);
                    crate::leanh::lean_dec(v_unused_3590_);
                    v___x_3543_ = v___x_3540_;
                    v_isShared_3544_ = v_isSharedCheck_3589_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3541_);
                    crate::leanh::lean_dec(v___x_3540_);
                    v___x_3543_ = crate::leanh::lean_box(0);
                    v_isShared_3544_ = v_isSharedCheck_3589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toFunctor_3545_ = crate::leanh::lean_ctor_get(v_toApplicative_3541_, 0);
                v_toSeq_3546_ = crate::leanh::lean_ctor_get(v_toApplicative_3541_, 2);
                v_toSeqLeft_3547_ = crate::leanh::lean_ctor_get(v_toApplicative_3541_, 3);
                v_toSeqRight_3548_ = crate::leanh::lean_ctor_get(v_toApplicative_3541_, 4);
                v_isSharedCheck_3587_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3541_)) as u8;
                if v_isSharedCheck_3587_ == 0 {
                    v_unused_3588_ = crate::leanh::lean_ctor_get(v_toApplicative_3541_, 1);
                    crate::leanh::lean_dec(v_unused_3588_);
                    v___x_3550_ = v_toApplicative_3541_;
                    v_isShared_3551_ = v_isSharedCheck_3587_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3548_);
                    crate::leanh::lean_inc(v_toSeqLeft_3547_);
                    crate::leanh::lean_inc(v_toSeq_3546_);
                    crate::leanh::lean_inc(v_toFunctor_3545_);
                    crate::leanh::lean_dec(v_toApplicative_3541_);
                    v___x_3550_ = crate::leanh::lean_box(0);
                    v_isShared_3551_ = v_isSharedCheck_3587_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___f_3552_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5;
                v___f_3553_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_3545_);
                v___f_3554_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3554_, 0, v_toFunctor_3545_);
                v___f_3555_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3555_, 0, v_toFunctor_3545_);
                v___x_3556_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3556_, 0, v___f_3554_);
                crate::leanh::lean_ctor_set(v___x_3556_, 1, v___f_3555_);
                v___f_3557_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3557_, 0, v_toSeqRight_3548_);
                v___f_3558_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3558_, 0, v_toSeqLeft_3547_);
                v___f_3559_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3559_, 0, v_toSeq_3546_);
                if v_isShared_3551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3550_, 4, v___f_3557_);
                    crate::leanh::lean_ctor_set(v___x_3550_, 3, v___f_3558_);
                    crate::leanh::lean_ctor_set(v___x_3550_, 2, v___f_3559_);
                    crate::leanh::lean_ctor_set(v___x_3550_, 1, v___f_3552_);
                    crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3556_);
                    v___x_3561_ = v___x_3550_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___f_3552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 2, v___f_3559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 3, v___f_3558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 4, v___f_3557_);
                    v___x_3561_ = v_reuseFailAlloc_3586_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3543_, 1, v___f_3553_);
                    crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3561_);
                    v___x_3563_ = v___x_3543_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___f_3553_);
                    v___x_3563_ = v_reuseFailAlloc_3585_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_sz_3564_ = lean_array_size(v_us_3517_);
                v___x_3565_ = 0usize;
                crate::leanh::lean_inc_ref(v_us_3517_);
                v___x_898__overap_3566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3563_,
                    v___f_3515_,
                    v_sz_3564_,
                    v___x_3565_,
                    v_us_3517_,
                );
                crate::leanh::lean_inc(v_a_3508_);
                crate::leanh::lean_inc_ref(v_a_3507_);
                crate::leanh::lean_inc(v_a_3506_);
                crate::leanh::lean_inc_ref(v_a_3505_);
                v___x_3567_ = crate::leanh::lean_apply_5(
                    v___x_898__overap_3566_,
                    v_a_3505_,
                    v_a_3506_,
                    v_a_3507_,
                    v_a_3508_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3567_) == 0 {
                    v_a_3568_ = crate::leanh::lean_ctor_get(v___x_3567_, 0);
                    v_isSharedCheck_3576_ = (!crate::leanh::lean_is_exclusive(v___x_3567_)) as u8;
                    if v_isSharedCheck_3576_ == 0 {
                        v___x_3570_ = v___x_3567_;
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3568_);
                        crate::leanh::lean_dec(v___x_3567_);
                        v___x_3570_ = crate::leanh::lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_us_3517_);
                    crate::leanh::lean_dec_ref(v_proof_3516_);
                    v_a_3577_ = crate::leanh::lean_ctor_get(v___x_3567_, 0);
                    v_isSharedCheck_3584_ = (!crate::leanh::lean_is_exclusive(v___x_3567_)) as u8;
                    if v_isSharedCheck_3584_ == 0 {
                        v___x_3579_ = v___x_3567_;
                        v_isShared_3580_ = v_isSharedCheck_3584_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3577_);
                        crate::leanh::lean_dec(v___x_3567_);
                        v___x_3579_ = crate::leanh::lean_box(0);
                        v_isShared_3580_ = v_isSharedCheck_3584_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3572_ =
                    l_Lean_Expr_instantiateLevelParamsArray(v_proof_3516_, v_us_3517_, v_a_3568_);
                crate::leanh::lean_dec_ref(v_proof_3516_);
                if v_isShared_3571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3570_, 0, v___x_3572_);
                    v___x_3574_ = v___x_3570_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
                    v___x_3574_ = v_reuseFailAlloc_3575_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3574_;
            }
            10 => {
                if v_isShared_3580_ == 0 {
                    v___x_3582_ = v___x_3579_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3582_;
            }
            12 => {
                v___x_3609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3609_, 0, v___x_3608_);
                crate::leanh::lean_ctor_set(v___x_3609_, 1, v___f_3600_);
                v___x_3610_ = l_StateRefT_x27_instMonad___redArg(v___x_3609_);
                v_toApplicative_3611_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                v_isSharedCheck_3667_ = (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                if v_isSharedCheck_3667_ == 0 {
                    v_unused_3668_ = crate::leanh::lean_ctor_get(v___x_3610_, 1);
                    crate::leanh::lean_dec(v_unused_3668_);
                    v___x_3613_ = v___x_3610_;
                    v_isShared_3614_ = v_isSharedCheck_3667_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3611_);
                    crate::leanh::lean_dec(v___x_3610_);
                    v___x_3613_ = crate::leanh::lean_box(0);
                    v_isShared_3614_ = v_isSharedCheck_3667_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_toFunctor_3615_ = crate::leanh::lean_ctor_get(v_toApplicative_3611_, 0);
                v_toSeq_3616_ = crate::leanh::lean_ctor_get(v_toApplicative_3611_, 2);
                v_toSeqLeft_3617_ = crate::leanh::lean_ctor_get(v_toApplicative_3611_, 3);
                v_toSeqRight_3618_ = crate::leanh::lean_ctor_get(v_toApplicative_3611_, 4);
                v_isSharedCheck_3665_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3611_)) as u8;
                if v_isSharedCheck_3665_ == 0 {
                    v_unused_3666_ = crate::leanh::lean_ctor_get(v_toApplicative_3611_, 1);
                    crate::leanh::lean_dec(v_unused_3666_);
                    v___x_3620_ = v_toApplicative_3611_;
                    v_isShared_3621_ = v_isSharedCheck_3665_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3618_);
                    crate::leanh::lean_inc(v_toSeqLeft_3617_);
                    crate::leanh::lean_inc(v_toSeq_3616_);
                    crate::leanh::lean_inc(v_toFunctor_3615_);
                    crate::leanh::lean_dec(v_toApplicative_3611_);
                    v___x_3620_ = crate::leanh::lean_box(0);
                    v_isShared_3621_ = v_isSharedCheck_3665_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___f_3622_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5;
                v___f_3623_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_3615_);
                v___f_3624_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3624_, 0, v_toFunctor_3615_);
                v___f_3625_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3625_, 0, v_toFunctor_3615_);
                v___x_3626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3626_, 0, v___f_3624_);
                crate::leanh::lean_ctor_set(v___x_3626_, 1, v___f_3625_);
                v___f_3627_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3627_, 0, v_toSeqRight_3618_);
                v___f_3628_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3628_, 0, v_toSeqLeft_3617_);
                v___f_3629_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3629_, 0, v_toSeq_3616_);
                if v_isShared_3621_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3620_, 4, v___f_3627_);
                    crate::leanh::lean_ctor_set(v___x_3620_, 3, v___f_3628_);
                    crate::leanh::lean_ctor_set(v___x_3620_, 2, v___f_3629_);
                    crate::leanh::lean_ctor_set(v___x_3620_, 1, v___f_3622_);
                    crate::leanh::lean_ctor_set(v___x_3620_, 0, v___x_3626_);
                    v___x_3631_ = v___x_3620_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___f_3622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 2, v___f_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 3, v___f_3628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 4, v___f_3627_);
                    v___x_3631_ = v_reuseFailAlloc_3664_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3613_, 1, v___f_3623_);
                    crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3631_);
                    v___x_3633_ = v___x_3613_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___f_3623_);
                    v___x_3633_ = v_reuseFailAlloc_3663_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3634_ = l_Lean_Meta_instMonadEnvMetaM;
                v___x_3635_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_once
                    ),
                    _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12,
                );
                v___x_3636_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_once
                    ),
                    _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18,
                );
                v_toMonadRef_3637_ = crate::leanh::lean_ctor_get(v___x_3636_, 0);
                v_declName_3638_ = l_Lean_Expr_constName_x21(v_proof_3516_);
                v___x_3639_ = l_Lean_Meta_instAddMessageContextMetaM;
                crate::leanh::lean_inc_ref(v___x_3633_);
                v___x_3640_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_3639_,
                    v___x_3633_,
                );
                crate::leanh::lean_inc_ref(v_toMonadRef_3637_);
                v___x_3641_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3635_);
                crate::leanh::lean_ctor_set(v___x_3641_, 1, v_toMonadRef_3637_);
                crate::leanh::lean_ctor_set(v___x_3641_, 2, v___x_3640_);
                crate::leanh::lean_inc(v_declName_3638_);
                v___x_886__overap_3642_ = l_Lean_getConstVal___redArg(
                    v___x_3633_,
                    v___x_3634_,
                    v___x_3641_,
                    v_declName_3638_,
                );
                crate::leanh::lean_inc(v_a_3508_);
                crate::leanh::lean_inc_ref(v_a_3507_);
                crate::leanh::lean_inc(v_a_3506_);
                crate::leanh::lean_inc_ref(v_a_3505_);
                v___x_3643_ = crate::leanh::lean_apply_5(
                    v___x_886__overap_3642_,
                    v_a_3505_,
                    v_a_3506_,
                    v_a_3507_,
                    v_a_3508_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3643_) == 0 {
                    v_a_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3654_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3646_ = v___x_3643_;
                        v_isShared_3647_ = v_isSharedCheck_3654_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3644_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3646_ = crate::leanh::lean_box(0);
                        v_isShared_3647_ = v_isSharedCheck_3654_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3638_);
                    crate::leanh::lean_dec_ref(v_proof_3516_);
                    v_a_3655_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3662_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3662_ == 0 {
                        v___x_3657_ = v___x_3643_;
                        v_isShared_3658_ = v_isSharedCheck_3662_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3655_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3657_ = crate::leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3662_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                v_levelParams_3648_ = crate::leanh::lean_ctor_get(v_a_3644_, 1);
                crate::leanh::lean_inc(v_levelParams_3648_);
                crate::leanh::lean_dec(v_a_3644_);
                v___x_3649_ = l_List_isEmpty___redArg(v_levelParams_3648_);
                crate::leanh::lean_dec(v_levelParams_3648_);
                if v___x_3649_ == 0 {
                    crate::leanh::lean_del_object(v___x_3646_);
                    crate::leanh::lean_dec_ref(v_proof_3516_);
                    v___x_3650_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                        v_declName_3638_,
                        v_a_3505_,
                        v_a_3506_,
                        v_a_3507_,
                        v_a_3508_,
                    );
                    return v___x_3650_;
                } else {
                    crate::leanh::lean_dec(v_declName_3638_);
                    if v_isShared_3647_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3646_, 0, v_proof_3516_);
                        v___x_3652_ = v___x_3646_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_proof_3516_);
                        v___x_3652_ = v_reuseFailAlloc_3653_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_3652_;
            }
            19 => {
                if v_isShared_3658_ == 0 {
                    v___x_3660_ = v___x_3657_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(
    mut v_inst_3678_: *mut crate::leanh::LeanObject,
    mut v_thm_3679_: *mut crate::leanh::LeanObject,
    mut v_a_3680_: *mut crate::leanh::LeanObject,
    mut v_a_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3685_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(
        v_inst_3678_,
        v_thm_3679_,
        v_a_3680_,
        v_a_3681_,
        v_a_3682_,
        v_a_3683_,
    );
    crate::leanh::lean_dec(v_a_3683_);
    crate::leanh::lean_dec_ref(v_a_3682_);
    crate::leanh::lean_dec(v_a_3681_);
    crate::leanh::lean_dec_ref(v_a_3680_);
    return v_res_3685_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels(
    mut v_00_u03b1_3686_: *mut crate::leanh::LeanObject,
    mut v_inst_3687_: *mut crate::leanh::LeanObject,
    mut v_thm_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
    mut v_a_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3694_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(
        v_inst_3687_,
        v_thm_3688_,
        v_a_3689_,
        v_a_3690_,
        v_a_3691_,
        v_a_3692_,
    );
    return v___x_3694_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(
    mut v_00_u03b1_3695_: *mut crate::leanh::LeanObject,
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
    mut v_thm_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_a_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3703_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(
        v_00_u03b1_3695_,
        v_inst_3696_,
        v_thm_3697_,
        v_a_3698_,
        v_a_3699_,
        v_a_3700_,
        v_a_3701_,
    );
    crate::leanh::lean_dec(v_a_3701_);
    crate::leanh::lean_dec_ref(v_a_3700_);
    crate::leanh::lean_dec(v_a_3699_);
    crate::leanh::lean_dec_ref(v_a_3698_);
    return v_res_3703_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(
    mut v_msgData_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = lean_st_ref_get(v___y_3708_);
    v_env_3711_ = crate::leanh::lean_ctor_get(v___x_3710_, 0);
    crate::leanh::lean_inc_ref(v_env_3711_);
    crate::leanh::lean_dec(v___x_3710_);
    v___x_3712_ = lean_st_ref_get(v___y_3706_);
    v_mctx_3713_ = crate::leanh::lean_ctor_get(v___x_3712_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3713_);
    crate::leanh::lean_dec(v___x_3712_);
    v_lctx_3714_ = crate::leanh::lean_ctor_get(v___y_3705_, 2);
    v_options_3715_ = crate::leanh::lean_ctor_get(v___y_3707_, 2);
    crate::leanh::lean_inc_ref(v_options_3715_);
    crate::leanh::lean_inc_ref(v_lctx_3714_);
    v___x_3716_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3716_, 0, v_env_3711_);
    crate::leanh::lean_ctor_set(v___x_3716_, 1, v_mctx_3713_);
    crate::leanh::lean_ctor_set(v___x_3716_, 2, v_lctx_3714_);
    crate::leanh::lean_ctor_set(v___x_3716_, 3, v_options_3715_);
    v___x_3717_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3717_, 0, v___x_3716_);
    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_msgData_3704_);
    v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(
    mut v_msgData_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    crate::leanh::lean_dec(v___y_3723_);
    crate::leanh::lean_dec_ref(v___y_3722_);
    crate::leanh::lean_dec(v___y_3721_);
    crate::leanh::lean_dec_ref(v___y_3720_);
    return v_res_3725_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(
    mut v_msg_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3732_ = crate::leanh::lean_ctor_get(v___y_3729_, 5);
                v___x_3733_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msg_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
                v_a_3734_ = crate::leanh::lean_ctor_get(v___x_3733_, 0);
                v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v___x_3733_)) as u8;
                if v_isSharedCheck_3742_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    v_isShared_3737_ = v_isSharedCheck_3742_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3734_);
                    crate::leanh::lean_dec(v___x_3733_);
                    v___x_3736_ = crate::leanh::lean_box(0);
                    v_isShared_3737_ = v_isSharedCheck_3742_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3732_);
                v___x_3738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3738_, 0, v_ref_3732_);
                crate::leanh::lean_ctor_set(v___x_3738_, 1, v_a_3734_);
                if v_isShared_3737_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3736_, 1);
                    crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3740_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
                    v___x_3740_ = v_reuseFailAlloc_3741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(
    mut v_msg_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3749_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(
        v_msg_3743_,
        v___y_3744_,
        v___y_3745_,
        v___y_3746_,
        v___y_3747_,
    );
    crate::leanh::lean_dec(v___y_3747_);
    crate::leanh::lean_dec_ref(v___y_3746_);
    crate::leanh::lean_dec(v___y_3745_);
    crate::leanh::lean_dec_ref(v___y_3744_);
    return v_res_3749_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0;
    v___x_3752_ = l_Lean_stringToMessageData(v___x_3751_);
    return v___x_3752_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2;
    v___x_3755_ = l_Lean_stringToMessageData(v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(
    mut v_declName_3756_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: u8 = 0;
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1,
    );
    v___x_3764_ = 0;
    v___x_3765_ = l_Lean_MessageData_ofConstName(v_declName_3756_, v___x_3764_);
    v___x_3766_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3766_, 0, v___x_3763_);
    crate::leanh::lean_ctor_set(v___x_3766_, 1, v___x_3765_);
    v___x_3767_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3,
    );
    v___x_3768_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3766_);
    crate::leanh::lean_ctor_set(v___x_3768_, 1, v___x_3767_);
    v___x_3769_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(
        v___x_3768_,
        v___y_3758_,
        v___y_3759_,
        v___y_3760_,
        v___y_3761_,
    );
    return v___x_3769_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(
    mut v_declName_3770_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3771_: *mut crate::leanh::LeanObject,
    mut v___y_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3777_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(
        v_declName_3770_,
        v_00_u03b1_3771_,
        v___y_3772_,
        v___y_3773_,
        v___y_3774_,
        v___y_3775_,
    );
    crate::leanh::lean_dec(v___y_3775_);
    crate::leanh::lean_dec_ref(v___y_3774_);
    crate::leanh::lean_dec(v___y_3773_);
    crate::leanh::lean_dec_ref(v___y_3772_);
    return v_res_3777_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(
    mut v_s_3778_: *mut crate::leanh::LeanObject,
    mut v___x_3779_: u8,
    mut v_as_3780_: *mut crate::leanh::LeanObject,
    mut v_i_3781_: usize,
    mut v_stop_3782_: usize,
) -> u8 {
    let mut v___x_3783_: u8 = 0;
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: usize = 0;
    let mut v___x_3789_: usize = 0;
    let mut v___x_3791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3783_ = lean_usize_dec_eq(v_i_3781_, v_stop_3782_);
                if v___x_3783_ == 0 {
                    v___x_3784_ = 1;
                    v___x_3785_ = lean_array_uget_borrowed(v_as_3780_, v_i_3781_);
                    crate::leanh::lean_inc(v___x_3785_);
                    v___x_3786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
                    v___x_3787_ =
                        l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_3778_, v___x_3786_);
                    crate::leanh::lean_dec_ref_known(v___x_3786_, 1);
                    if v___x_3787_ == 0 {
                        return v___x_3784_;
                    } else {
                        if v___x_3779_ == 0 {
                            v___x_3788_ = 1usize;
                            v___x_3789_ = lean_usize_add(v_i_3781_, v___x_3788_);
                            v_i_3781_ = v___x_3789_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_3784_;
                        }
                    }
                } else {
                    v___x_3791_ = 0;
                    return v___x_3791_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(
    mut v_s_3792_: *mut crate::leanh::LeanObject,
    mut v___x_3793_: *mut crate::leanh::LeanObject,
    mut v_as_3794_: *mut crate::leanh::LeanObject,
    mut v_i_3795_: *mut crate::leanh::LeanObject,
    mut v_stop_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3292__boxed_3797_: u8 = 0;
    let mut v_i_boxed_3798_: usize = 0;
    let mut v_stop_boxed_3799_: usize = 0;
    let mut v_res_3800_: u8 = 0;
    let mut v_r_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3292__boxed_3797_ = (crate::leanh::lean_unbox(v___x_3793_) as u8);
    v_i_boxed_3798_ = crate::leanh::lean_unbox_usize(v_i_3795_);
    crate::leanh::lean_dec(v_i_3795_);
    v_stop_boxed_3799_ = crate::leanh::lean_unbox_usize(v_stop_3796_);
    crate::leanh::lean_dec(v_stop_3796_);
    v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_3792_, v___x_3292__boxed_3797_, v_as_3794_, v_i_boxed_3798_, v_stop_boxed_3799_);
    crate::leanh::lean_dec_ref(v_as_3794_);
    crate::leanh::lean_dec_ref(v_s_3792_);
    v_r_3801_ = crate::leanh::lean_box((v_res_3800_) as usize);
    return v_r_3801_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(
    mut v_as_3802_: *mut crate::leanh::LeanObject,
    mut v_i_3803_: usize,
    mut v_stop_3804_: usize,
    mut v_b_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3806_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: usize = 0;
    let mut v___x_3811_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3806_ = lean_usize_dec_eq(v_i_3803_, v_stop_3804_);
                if v___x_3806_ == 0 {
                    v___x_3807_ = lean_array_uget_borrowed(v_as_3802_, v_i_3803_);
                    crate::leanh::lean_inc(v___x_3807_);
                    v___x_3808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3807_);
                    v___x_3809_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_b_3805_, v___x_3808_);
                    v___x_3810_ = 1usize;
                    v___x_3811_ = lean_usize_add(v_i_3803_, v___x_3810_);
                    v_i_3803_ = v___x_3811_;
                    v_b_3805_ = v___x_3809_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3805_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(
    mut v_as_3813_: *mut crate::leanh::LeanObject,
    mut v_i_3814_: *mut crate::leanh::LeanObject,
    mut v_stop_3815_: *mut crate::leanh::LeanObject,
    mut v_b_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3817_: usize = 0;
    let mut v_stop_boxed_3818_: usize = 0;
    let mut v_res_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3817_ = crate::leanh::lean_unbox_usize(v_i_3814_);
    crate::leanh::lean_dec(v_i_3814_);
    v_stop_boxed_3818_ = crate::leanh::lean_unbox_usize(v_stop_3815_);
    crate::leanh::lean_dec(v_stop_3815_);
    v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_3813_, v_i_boxed_3817_, v_stop_boxed_3818_, v_b_3816_);
    crate::leanh::lean_dec_ref(v_as_3813_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(
    mut v_s_3820_: *mut crate::leanh::LeanObject,
    mut v_declName_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v_val_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: usize = 0;
    let mut v___x_3852_: usize = 0;
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: usize = 0;
    let mut v___x_3858_: usize = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: usize = 0;
    let mut v___x_3867_: usize = 0;
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: u8 = 0;
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3831_ = lean_st_ref_get(v_a_3825_);
                v_env_3832_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                crate::leanh::lean_inc_ref(v_env_3832_);
                crate::leanh::lean_dec(v___x_3831_);
                crate::leanh::lean_inc(v_declName_3821_);
                v___x_3833_ = l_Lean_wasOriginallyTheorem(v_env_3832_, v_declName_3821_);
                if v___x_3833_ == 0 {
                    crate::leanh::lean_inc(v_declName_3821_);
                    v___x_3834_ = l_Lean_Meta_getEqnsFor_x3f(
                        v_declName_3821_,
                        v_a_3822_,
                        v_a_3823_,
                        v_a_3824_,
                        v_a_3825_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3834_) == 0 {
                        v_a_3835_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                        v_isSharedCheck_3879_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3834_)) as u8;
                        if v_isSharedCheck_3879_ == 0 {
                            v___x_3837_ = v___x_3834_;
                            v_isShared_3838_ = v_isSharedCheck_3879_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3835_);
                            crate::leanh::lean_dec(v___x_3834_);
                            v___x_3837_ = crate::leanh::lean_box(0);
                            v_isShared_3838_ = v_isSharedCheck_3879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_3821_);
                        crate::leanh::lean_dec_ref(v_s_3820_);
                        v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                        v_isSharedCheck_3887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3834_)) as u8;
                        if v_isSharedCheck_3887_ == 0 {
                            v___x_3882_ = v___x_3834_;
                            v_isShared_3883_ = v_isSharedCheck_3887_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3880_);
                            crate::leanh::lean_dec(v___x_3834_);
                            v___x_3882_ = crate::leanh::lean_box(0);
                            v_isShared_3883_ = v_isSharedCheck_3887_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_declName_3821_);
                    v___x_3888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3888_, 0, v_declName_3821_);
                    v___x_3889_ =
                        l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_3820_, v___x_3888_);
                    crate::leanh::lean_dec_ref_known(v___x_3888_, 1);
                    if v___x_3889_ == 0 {
                        crate::leanh::lean_dec_ref(v_s_3820_);
                        v___x_3890_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(
                            v_declName_3821_,
                            crate::leanh::lean_box(0),
                            v_a_3822_,
                            v_a_3823_,
                            v_a_3824_,
                            v_a_3825_,
                        );
                        v_a_3891_ = crate::leanh::lean_ctor_get(v___x_3890_, 0);
                        v_isSharedCheck_3898_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3890_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3890_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3891_);
                            crate::leanh::lean_dec(v___x_3890_);
                            v___x_3893_ = crate::leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 12;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3828_, 0, v_declName_3821_);
                v___x_3829_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_3820_, v___x_3828_);
                v___x_3830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                return v___x_3830_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3835_) == 1 {
                    v_val_3839_ = crate::leanh::lean_ctor_get(v_a_3835_, 0);
                    crate::leanh::lean_inc(v_val_3839_);
                    crate::leanh::lean_dec_ref_known(v_a_3835_, 1);
                    v___x_3863_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3864_ = lean_array_get_size(v_val_3839_);
                    v___x_3865_ = lean_nat_dec_lt(v___x_3863_, v___x_3864_);
                    if v___x_3865_ == 0 {
                        crate::leanh::lean_dec(v_declName_3821_);
                        state = 3;
                        continue;
                    } else {
                        if v___x_3865_ == 0 {
                            crate::leanh::lean_dec(v_declName_3821_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3866_ = 0usize;
                            v___x_3867_ = lean_usize_of_nat(v___x_3864_);
                            v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_3820_, v___x_3833_, v_val_3839_, v___x_3866_, v___x_3867_);
                            if v___x_3868_ == 0 {
                                crate::leanh::lean_dec(v_declName_3821_);
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_3839_);
                                crate::leanh::lean_del_object(v___x_3837_);
                                crate::leanh::lean_dec_ref(v_s_3820_);
                                v___x_3869_ =
                                    l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(
                                        v_declName_3821_,
                                        crate::leanh::lean_box(0),
                                        v_a_3822_,
                                        v_a_3823_,
                                        v_a_3824_,
                                        v_a_3825_,
                                    );
                                v_a_3870_ = crate::leanh::lean_ctor_get(v___x_3869_, 0);
                                v_isSharedCheck_3877_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3869_)) as u8;
                                if v_isSharedCheck_3877_ == 0 {
                                    v___x_3872_ = v___x_3869_;
                                    v_isShared_3873_ = v_isSharedCheck_3877_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3870_);
                                    crate::leanh::lean_dec(v___x_3869_);
                                    v___x_3872_ = crate::leanh::lean_box(0);
                                    v_isShared_3873_ = v_isSharedCheck_3877_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3837_);
                    crate::leanh::lean_dec(v_a_3835_);
                    crate::leanh::lean_dec_ref(v_s_3820_);
                    v___x_3878_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(
                        v_declName_3821_,
                        crate::leanh::lean_box(0),
                        v_a_3822_,
                        v_a_3823_,
                        v_a_3824_,
                        v_a_3825_,
                    );
                    return v___x_3878_;
                }
            }
            3 => {
                v___x_3841_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3842_ = lean_array_get_size(v_val_3839_);
                v___x_3843_ = lean_nat_dec_lt(v___x_3841_, v___x_3842_);
                if v___x_3843_ == 0 {
                    crate::leanh::lean_dec(v_val_3839_);
                    if v_isShared_3838_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3837_, 0, v_s_3820_);
                        v___x_3845_ = v___x_3837_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_s_3820_);
                        v___x_3845_ = v_reuseFailAlloc_3846_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3847_ = lean_nat_dec_le(v___x_3842_, v___x_3842_);
                    if v___x_3847_ == 0 {
                        if v___x_3843_ == 0 {
                            crate::leanh::lean_dec(v_val_3839_);
                            if v_isShared_3838_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3837_, 0, v_s_3820_);
                                v___x_3849_ = v___x_3837_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_3850_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_s_3820_);
                                v___x_3849_ = v_reuseFailAlloc_3850_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_3851_ = 0usize;
                            v___x_3852_ = lean_usize_of_nat(v___x_3842_);
                            v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_3839_, v___x_3851_, v___x_3852_, v_s_3820_);
                            crate::leanh::lean_dec(v_val_3839_);
                            if v_isShared_3838_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3837_, 0, v___x_3853_);
                                v___x_3855_ = v___x_3837_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3856_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
                                v___x_3855_ = v_reuseFailAlloc_3856_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_3857_ = 0usize;
                        v___x_3858_ = lean_usize_of_nat(v___x_3842_);
                        v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_3839_, v___x_3857_, v___x_3858_, v_s_3820_);
                        crate::leanh::lean_dec(v_val_3839_);
                        if v_isShared_3838_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3837_, 0, v___x_3859_);
                            v___x_3861_ = v___x_3837_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3862_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
                            v___x_3861_ = v_reuseFailAlloc_3862_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3845_;
            }
            5 => {
                return v___x_3849_;
            }
            6 => {
                return v___x_3855_;
            }
            7 => {
                return v___x_3861_;
            }
            8 => {
                if v_isShared_3873_ == 0 {
                    v___x_3875_ = v___x_3872_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
                    v___x_3875_ = v_reuseFailAlloc_3876_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3875_;
            }
            10 => {
                if v_isShared_3883_ == 0 {
                    v___x_3885_ = v___x_3882_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
                    v___x_3885_ = v_reuseFailAlloc_3886_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3885_;
            }
            12 => {
                if v_isShared_3894_ == 0 {
                    v___x_3896_ = v___x_3893_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(
    mut v_s_3899_: *mut crate::leanh::LeanObject,
    mut v_declName_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
    mut v_a_3903_: *mut crate::leanh::LeanObject,
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(
        v_s_3899_,
        v_declName_3900_,
        v_a_3901_,
        v_a_3902_,
        v_a_3903_,
        v_a_3904_,
    );
    crate::leanh::lean_dec(v_a_3904_);
    crate::leanh::lean_dec_ref(v_a_3903_);
    crate::leanh::lean_dec(v_a_3902_);
    crate::leanh::lean_dec_ref(v_a_3901_);
    return v_res_3906_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl(
    mut v_00_u03b1_3907_: *mut crate::leanh::LeanObject,
    mut v_s_3908_: *mut crate::leanh::LeanObject,
    mut v_declName_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(
        v_s_3908_,
        v_declName_3909_,
        v_a_3910_,
        v_a_3911_,
        v_a_3912_,
        v_a_3913_,
    );
    return v___x_3915_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(
    mut v_00_u03b1_3916_: *mut crate::leanh::LeanObject,
    mut v_s_3917_: *mut crate::leanh::LeanObject,
    mut v_declName_3918_: *mut crate::leanh::LeanObject,
    mut v_a_3919_: *mut crate::leanh::LeanObject,
    mut v_a_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3924_ = l_Lean_Meta_Grind_Theorems_eraseDecl(
        v_00_u03b1_3916_,
        v_s_3917_,
        v_declName_3918_,
        v_a_3919_,
        v_a_3920_,
        v_a_3921_,
        v_a_3922_,
    );
    crate::leanh::lean_dec(v_a_3922_);
    crate::leanh::lean_dec_ref(v_a_3921_);
    crate::leanh::lean_dec(v_a_3920_);
    crate::leanh::lean_dec_ref(v_a_3919_);
    return v_res_3924_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(
    mut v_00_u03b1_3925_: *mut crate::leanh::LeanObject,
    mut v_msg_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(
        v_msg_3926_,
        v___y_3927_,
        v___y_3928_,
        v___y_3929_,
        v___y_3930_,
    );
    return v___x_3932_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(
    mut v_00_u03b1_3933_: *mut crate::leanh::LeanObject,
    mut v_msg_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(
        v_00_u03b1_3933_,
        v_msg_3934_,
        v___y_3935_,
        v___y_3936_,
        v___y_3937_,
        v___y_3938_,
    );
    crate::leanh::lean_dec(v___y_3938_);
    crate::leanh::lean_dec_ref(v___y_3937_);
    crate::leanh::lean_dec(v___y_3936_);
    crate::leanh::lean_dec_ref(v___y_3935_);
    return v_res_3940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(
    mut v_00_u03b1_3941_: *mut crate::leanh::LeanObject,
    mut v_as_3942_: *mut crate::leanh::LeanObject,
    mut v_i_3943_: usize,
    mut v_stop_3944_: usize,
    mut v_b_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_3942_, v_i_3943_, v_stop_3944_, v_b_3945_);
    return v___x_3946_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(
    mut v_00_u03b1_3947_: *mut crate::leanh::LeanObject,
    mut v_as_3948_: *mut crate::leanh::LeanObject,
    mut v_i_3949_: *mut crate::leanh::LeanObject,
    mut v_stop_3950_: *mut crate::leanh::LeanObject,
    mut v_b_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3952_: usize = 0;
    let mut v_stop_boxed_3953_: usize = 0;
    let mut v_res_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3952_ = crate::leanh::lean_unbox_usize(v_i_3949_);
    crate::leanh::lean_dec(v_i_3949_);
    v_stop_boxed_3953_ = crate::leanh::lean_unbox_usize(v_stop_3950_);
    crate::leanh::lean_dec(v_stop_3950_);
    v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(v_00_u03b1_3947_, v_as_3948_, v_i_boxed_3952_, v_stop_boxed_3953_, v_b_3951_);
    crate::leanh::lean_dec_ref(v_as_3948_);
    return v_res_3954_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(
    mut v_00_u03b1_3955_: *mut crate::leanh::LeanObject,
    mut v_s_3956_: *mut crate::leanh::LeanObject,
    mut v___x_3957_: u8,
    mut v_as_3958_: *mut crate::leanh::LeanObject,
    mut v_i_3959_: usize,
    mut v_stop_3960_: usize,
) -> u8 {
    let mut v___x_3961_: u8 = 0;
    v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_3956_, v___x_3957_, v_as_3958_, v_i_3959_, v_stop_3960_);
    return v___x_3961_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(
    mut v_00_u03b1_3962_: *mut crate::leanh::LeanObject,
    mut v_s_3963_: *mut crate::leanh::LeanObject,
    mut v___x_3964_: *mut crate::leanh::LeanObject,
    mut v_as_3965_: *mut crate::leanh::LeanObject,
    mut v_i_3966_: *mut crate::leanh::LeanObject,
    mut v_stop_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3498__boxed_3968_: u8 = 0;
    let mut v_i_boxed_3969_: usize = 0;
    let mut v_stop_boxed_3970_: usize = 0;
    let mut v_res_3971_: u8 = 0;
    let mut v_r_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3498__boxed_3968_ = (crate::leanh::lean_unbox(v___x_3964_) as u8);
    v_i_boxed_3969_ = crate::leanh::lean_unbox_usize(v_i_3966_);
    crate::leanh::lean_dec(v_i_3966_);
    v_stop_boxed_3970_ = crate::leanh::lean_unbox_usize(v_stop_3967_);
    crate::leanh::lean_dec(v_stop_3967_);
    v_res_3971_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(v_00_u03b1_3962_, v_s_3963_, v___x_3498__boxed_3968_, v_as_3965_, v_i_boxed_3969_, v_stop_boxed_3970_);
    crate::leanh::lean_dec_ref(v_as_3965_);
    crate::leanh::lean_dec_ref(v_s_3963_);
    v_r_3972_ = crate::leanh::lean_box((v_res_3971_) as usize);
    return v_r_3972_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(
    mut v_a_3973_: *mut crate::leanh::LeanObject,
    mut v_a_3974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v_fst_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3973_) == 0 {
                    v___x_3975_ = l_List_reverse___redArg(v_a_3974_);
                    return v___x_3975_;
                } else {
                    v_head_3976_ = crate::leanh::lean_ctor_get(v_a_3973_, 0);
                    v_tail_3977_ = crate::leanh::lean_ctor_get(v_a_3973_, 1);
                    v_isSharedCheck_3986_ = (!crate::leanh::lean_is_exclusive(v_a_3973_)) as u8;
                    if v_isSharedCheck_3986_ == 0 {
                        v___x_3979_ = v_a_3973_;
                        v_isShared_3980_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3977_);
                        crate::leanh::lean_inc(v_head_3976_);
                        crate::leanh::lean_dec(v_a_3973_);
                        v___x_3979_ = crate::leanh::lean_box(0);
                        v_isShared_3980_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3981_ = crate::leanh::lean_ctor_get(v_head_3976_, 0);
                crate::leanh::lean_inc(v_fst_3981_);
                crate::leanh::lean_dec(v_head_3976_);
                if v_isShared_3980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3979_, 1, v_a_3974_);
                    crate::leanh::lean_ctor_set(v___x_3979_, 0, v_fst_3981_);
                    v___x_3983_ = v___x_3979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_fst_3981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_a_3974_);
                    v___x_3983_ = v_reuseFailAlloc_3985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3973_ = v_tail_3977_;
                v_a_3974_ = v___x_3983_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(
    mut v_ps_3987_: *mut crate::leanh::LeanObject,
    mut v_k_3988_: *mut crate::leanh::LeanObject,
    mut v_v_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3990_, 0, v_k_3988_);
    crate::leanh::lean_ctor_set(v___x_3990_, 1, v_v_3989_);
    v___x_3991_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3991_, 0, v___x_3990_);
    crate::leanh::lean_ctor_set(v___x_3991_, 1, v_ps_3987_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(
    mut v_f_3992_: *mut crate::leanh::LeanObject,
    mut v_x1_3993_: *mut crate::leanh::LeanObject,
    mut v_x2_3994_: *mut crate::leanh::LeanObject,
    mut v_x3_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = crate::leanh::lean_apply_3(v_f_3992_, v_x1_3993_, v_x2_3994_, v_x3_3995_);
    return v___x_3996_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_f_3997_: *mut crate::leanh::LeanObject,
    mut v_keys_3998_: *mut crate::leanh::LeanObject,
    mut v_vals_3999_: *mut crate::leanh::LeanObject,
    mut v_i_4000_: *mut crate::leanh::LeanObject,
    mut v_acc_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    let mut v_k_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4002_ = lean_array_get_size(v_keys_3998_);
                v___x_4003_ = lean_nat_dec_lt(v_i_4000_, v___x_4002_);
                if v___x_4003_ == 0 {
                    crate::leanh::lean_dec(v_i_4000_);
                    crate::leanh::lean_dec(v_f_3997_);
                    return v_acc_4001_;
                } else {
                    v_k_4004_ = lean_array_fget_borrowed(v_keys_3998_, v_i_4000_);
                    v_v_4005_ = lean_array_fget_borrowed(v_vals_3999_, v_i_4000_);
                    crate::leanh::lean_inc(v_f_3997_);
                    crate::leanh::lean_inc(v_v_4005_);
                    crate::leanh::lean_inc(v_k_4004_);
                    v___x_4006_ =
                        crate::leanh::lean_apply_3(v_f_3997_, v_acc_4001_, v_k_4004_, v_v_4005_);
                    v___x_4007_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4008_ = lean_nat_add(v_i_4000_, v___x_4007_);
                    crate::leanh::lean_dec(v_i_4000_);
                    v_i_4000_ = v___x_4008_;
                    v_acc_4001_ = v___x_4006_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_f_4010_: *mut crate::leanh::LeanObject,
    mut v_keys_4011_: *mut crate::leanh::LeanObject,
    mut v_vals_4012_: *mut crate::leanh::LeanObject,
    mut v_i_4013_: *mut crate::leanh::LeanObject,
    mut v_acc_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_4010_, v_keys_4011_, v_vals_4012_, v_i_4013_, v_acc_4014_);
    crate::leanh::lean_dec_ref(v_vals_4012_);
    crate::leanh::lean_dec_ref(v_keys_4011_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_f_4016_: *mut crate::leanh::LeanObject,
    mut v_x_4017_: *mut crate::leanh::LeanObject,
    mut v_x_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4017_) == 0 {
        let mut v_es_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: u8 = 0;
        v_es_4019_ = crate::leanh::lean_ctor_get(v_x_4017_, 0);
        v___x_4020_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4021_ = lean_array_get_size(v_es_4019_);
        v___x_4022_ = lean_nat_dec_lt(v___x_4020_, v___x_4021_);
        if v___x_4022_ == 0 {
            crate::leanh::lean_dec(v_f_4016_);
            return v_x_4018_;
        } else {
            let mut v___x_4023_: u8 = 0;
            v___x_4023_ = lean_nat_dec_le(v___x_4021_, v___x_4021_);
            if v___x_4023_ == 0 {
                if v___x_4022_ == 0 {
                    crate::leanh::lean_dec(v_f_4016_);
                    return v_x_4018_;
                } else {
                    let mut v___x_4024_: usize = 0;
                    let mut v___x_4025_: usize = 0;
                    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_4024_ = 0usize;
                    v___x_4025_ = lean_usize_of_nat(v___x_4021_);
                    v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_4016_, v_es_4019_, v___x_4024_, v___x_4025_, v_x_4018_);
                    return v___x_4026_;
                }
            } else {
                let mut v___x_4027_: usize = 0;
                let mut v___x_4028_: usize = 0;
                let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4027_ = 0usize;
                v___x_4028_ = lean_usize_of_nat(v___x_4021_);
                v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_4016_, v_es_4019_, v___x_4027_, v___x_4028_, v_x_4018_);
                return v___x_4029_;
            }
        }
    } else {
        let mut v_ks_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_4030_ = crate::leanh::lean_ctor_get(v_x_4017_, 0);
        v_vs_4031_ = crate::leanh::lean_ctor_get(v_x_4017_, 1);
        v___x_4032_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_4016_, v_ks_4030_, v_vs_4031_, v___x_4032_, v_x_4018_);
        return v___x_4033_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_f_4034_: *mut crate::leanh::LeanObject,
    mut v_as_4035_: *mut crate::leanh::LeanObject,
    mut v_i_4036_: usize,
    mut v_stop_4037_: usize,
    mut v_b_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: usize = 0;
    let mut v___x_4042_: usize = 0;
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4044_ = lean_usize_dec_eq(v_i_4036_, v_stop_4037_);
                if v___x_4044_ == 0 {
                    v___x_4045_ = lean_array_uget_borrowed(v_as_4035_, v_i_4036_);
                    match crate::leanh::lean_obj_tag(v___x_4045_) {
                        0 => {
                            v_key_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                            v_val_4047_ = crate::leanh::lean_ctor_get(v___x_4045_, 1);
                            crate::leanh::lean_inc(v_f_4034_);
                            crate::leanh::lean_inc(v_val_4047_);
                            crate::leanh::lean_inc(v_key_4046_);
                            v___x_4048_ = crate::leanh::lean_apply_3(
                                v_f_4034_,
                                v_b_4038_,
                                v_key_4046_,
                                v_val_4047_,
                            );
                            v___y_4040_ = v___x_4048_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_4049_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                            crate::leanh::lean_inc(v_f_4034_);
                            v___x_4050_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_4034_, v_node_4049_, v_b_4038_);
                            v___y_4040_ = v___x_4050_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_4040_ = v_b_4038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_4034_);
                    return v_b_4038_;
                }
            }
            1 => {
                v___x_4041_ = 1usize;
                v___x_4042_ = lean_usize_add(v_i_4036_, v___x_4041_);
                v_i_4036_ = v___x_4042_;
                v_b_4038_ = v___y_4040_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(
    mut v_f_4051_: *mut crate::leanh::LeanObject,
    mut v_as_4052_: *mut crate::leanh::LeanObject,
    mut v_i_4053_: *mut crate::leanh::LeanObject,
    mut v_stop_4054_: *mut crate::leanh::LeanObject,
    mut v_b_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4056_: usize = 0;
    let mut v_stop_boxed_4057_: usize = 0;
    let mut v_res_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4056_ = crate::leanh::lean_unbox_usize(v_i_4053_);
    crate::leanh::lean_dec(v_i_4053_);
    v_stop_boxed_4057_ = crate::leanh::lean_unbox_usize(v_stop_4054_);
    crate::leanh::lean_dec(v_stop_4054_);
    v_res_4058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_4051_, v_as_4052_, v_i_boxed_4056_, v_stop_boxed_4057_, v_b_4055_);
    crate::leanh::lean_dec_ref(v_as_4052_);
    return v_res_4058_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_f_4059_: *mut crate::leanh::LeanObject,
    mut v_x_4060_: *mut crate::leanh::LeanObject,
    mut v_x_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_4059_, v_x_4060_, v_x_4061_);
    crate::leanh::lean_dec_ref(v_x_4060_);
    return v_res_4062_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(
    mut v_map_4063_: *mut crate::leanh::LeanObject,
    mut v_f_4064_: *mut crate::leanh::LeanObject,
    mut v_init_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4066_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_4066_, 0, v_f_4064_);
    v___x_4067_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v___f_4066_, v_map_4063_, v_init_4065_);
    return v___x_4067_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_map_4068_: *mut crate::leanh::LeanObject,
    mut v_f_4069_: *mut crate::leanh::LeanObject,
    mut v_init_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_4068_, v_f_4069_, v_init_4070_);
    crate::leanh::lean_dec_ref(v_map_4068_);
    return v_res_4071_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(
    mut v_m_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4074_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0;
    v___x_4075_ = crate::leanh::lean_box(0);
    v___x_4076_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_m_4073_, v___f_4074_, v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(
    mut v_m_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_4077_);
    crate::leanh::lean_dec_ref(v_m_4077_);
    return v_res_4078_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(
    mut v_s_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_s_4079_);
    v___x_4081_ = crate::leanh::lean_box(0);
    v___x_4082_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(v___x_4080_, v___x_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(
    mut v_s_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ =
        l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(
            v_s_4083_,
        );
    crate::leanh::lean_dec_ref(v_s_4083_);
    return v_res_4084_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_getOrigins___redArg(
    mut v_s_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_origins_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_origins_4086_ = crate::leanh::lean_ctor_get(v_s_4085_, 1);
    v___x_4087_ =
        l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(
            v_origins_4086_,
        );
    return v___x_4087_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(
    mut v_s_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4089_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_4088_);
    crate::leanh::lean_dec_ref(v_s_4088_);
    return v_res_4089_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_getOrigins(
    mut v_00_u03b1_4090_: *mut crate::leanh::LeanObject,
    mut v_s_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_4091_);
    return v___x_4092_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_getOrigins___boxed(
    mut v_00_u03b1_4093_: *mut crate::leanh::LeanObject,
    mut v_s_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4095_ = l_Lean_Meta_Grind_Theorems_getOrigins(v_00_u03b1_4093_, v_s_4094_);
    crate::leanh::lean_dec_ref(v_s_4094_);
    return v_res_4095_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(
    mut v_00_u03b2_4096_: *mut crate::leanh::LeanObject,
    mut v_m_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(
    mut v_00_u03b2_4099_: *mut crate::leanh::LeanObject,
    mut v_m_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4101_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(v_00_u03b2_4099_, v_m_4100_);
    crate::leanh::lean_dec_ref(v_m_4100_);
    return v_res_4101_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(
    mut v_00_u03c3_4102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4103_: *mut crate::leanh::LeanObject,
    mut v_map_4104_: *mut crate::leanh::LeanObject,
    mut v_f_4105_: *mut crate::leanh::LeanObject,
    mut v_init_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_4104_, v_f_4105_, v_init_4106_);
    return v___x_4107_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_4108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4109_: *mut crate::leanh::LeanObject,
    mut v_map_4110_: *mut crate::leanh::LeanObject,
    mut v_f_4111_: *mut crate::leanh::LeanObject,
    mut v_init_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4113_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(v_00_u03c3_4108_, v_00_u03b2_4109_, v_map_4110_, v_f_4111_, v_init_4112_);
    crate::leanh::lean_dec_ref(v_map_4110_);
    return v_res_4113_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_map_4114_: *mut crate::leanh::LeanObject,
    mut v_f_4115_: *mut crate::leanh::LeanObject,
    mut v_init_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_4115_, v_map_4114_, v_init_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_map_4118_: *mut crate::leanh::LeanObject,
    mut v_f_4119_: *mut crate::leanh::LeanObject,
    mut v_init_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(v_map_4118_, v_f_4119_, v_init_4120_);
    crate::leanh::lean_dec_ref(v_map_4118_);
    return v_res_4121_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03c3_4122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4123_: *mut crate::leanh::LeanObject,
    mut v_map_4124_: *mut crate::leanh::LeanObject,
    mut v_f_4125_: *mut crate::leanh::LeanObject,
    mut v_init_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_4125_, v_map_4124_, v_init_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03c3_4128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4129_: *mut crate::leanh::LeanObject,
    mut v_map_4130_: *mut crate::leanh::LeanObject,
    mut v_f_4131_: *mut crate::leanh::LeanObject,
    mut v_init_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(v_00_u03c3_4128_, v_00_u03b2_4129_, v_map_4130_, v_f_4131_, v_init_4132_);
    crate::leanh::lean_dec_ref(v_map_4130_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03c3_4134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4135_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4136_: *mut crate::leanh::LeanObject,
    mut v_f_4137_: *mut crate::leanh::LeanObject,
    mut v_x_4138_: *mut crate::leanh::LeanObject,
    mut v_x_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_4137_, v_x_4138_, v_x_4139_);
    return v___x_4140_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03c3_4141_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4143_: *mut crate::leanh::LeanObject,
    mut v_f_4144_: *mut crate::leanh::LeanObject,
    mut v_x_4145_: *mut crate::leanh::LeanObject,
    mut v_x_4146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03c3_4141_, v_00_u03b1_4142_, v_00_u03b2_4143_, v_f_4144_, v_x_4145_, v_x_4146_);
    crate::leanh::lean_dec_ref(v_x_4145_);
    return v_res_4147_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b1_4148_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4149_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4150_: *mut crate::leanh::LeanObject,
    mut v_f_4151_: *mut crate::leanh::LeanObject,
    mut v_as_4152_: *mut crate::leanh::LeanObject,
    mut v_i_4153_: usize,
    mut v_stop_4154_: usize,
    mut v_b_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_4151_, v_as_4152_, v_i_4153_, v_stop_4154_, v_b_4155_);
    return v___x_4156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(
    mut v_00_u03b1_4157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4158_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4159_: *mut crate::leanh::LeanObject,
    mut v_f_4160_: *mut crate::leanh::LeanObject,
    mut v_as_4161_: *mut crate::leanh::LeanObject,
    mut v_i_4162_: *mut crate::leanh::LeanObject,
    mut v_stop_4163_: *mut crate::leanh::LeanObject,
    mut v_b_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4165_: usize = 0;
    let mut v_stop_boxed_4166_: usize = 0;
    let mut v_res_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4165_ = crate::leanh::lean_unbox_usize(v_i_4162_);
    crate::leanh::lean_dec(v_i_4162_);
    v_stop_boxed_4166_ = crate::leanh::lean_unbox_usize(v_stop_4163_);
    crate::leanh::lean_dec(v_stop_4163_);
    v_res_4167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_00_u03b1_4157_, v_00_u03b2_4158_, v_00_u03c3_4159_, v_f_4160_, v_as_4161_, v_i_boxed_4165_, v_stop_boxed_4166_, v_b_4164_);
    crate::leanh::lean_dec_ref(v_as_4161_);
    return v_res_4167_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03c3_4168_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4169_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4170_: *mut crate::leanh::LeanObject,
    mut v_f_4171_: *mut crate::leanh::LeanObject,
    mut v_keys_4172_: *mut crate::leanh::LeanObject,
    mut v_vals_4173_: *mut crate::leanh::LeanObject,
    mut v_heq_4174_: *mut crate::leanh::LeanObject,
    mut v_i_4175_: *mut crate::leanh::LeanObject,
    mut v_acc_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_4171_, v_keys_4172_, v_vals_4173_, v_i_4175_, v_acc_4176_);
    return v___x_4177_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03c3_4178_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4179_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4180_: *mut crate::leanh::LeanObject,
    mut v_f_4181_: *mut crate::leanh::LeanObject,
    mut v_keys_4182_: *mut crate::leanh::LeanObject,
    mut v_vals_4183_: *mut crate::leanh::LeanObject,
    mut v_heq_4184_: *mut crate::leanh::LeanObject,
    mut v_i_4185_: *mut crate::leanh::LeanObject,
    mut v_acc_4186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4187_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03c3_4178_, v_00_u03b1_4179_, v_00_u03b2_4180_, v_f_4181_, v_keys_4182_, v_vals_4183_, v_heq_4184_, v_i_4185_, v_acc_4186_);
    crate::leanh::lean_dec_ref(v_vals_4183_);
    crate::leanh::lean_dec_ref(v_keys_4182_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_Meta_Grind_Theorems_mkEmpty(
    mut v_00_u03b1_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4189_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3,
    );
    return v___x_4189_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4190_ = l_Lean_Meta_Grind_Theorems_mkEmpty(crate::leanh::lean_box(0));
    return v___x_4190_;
}
pub unsafe fn l_Lean_Meta_Grind_instEmptyCollectionTheorems(
    mut v_00_u03b1_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0_once),
        _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0,
    );
    return v___x_4192_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4193_) == 0 {
                    v___x_4195_ = l_List_reverse___redArg(v_a_4194_);
                    return v___x_4195_;
                } else {
                    v_head_4196_ = crate::leanh::lean_ctor_get(v_a_4193_, 0);
                    v_tail_4197_ = crate::leanh::lean_ctor_get(v_a_4193_, 1);
                    v_isSharedCheck_4206_ = (!crate::leanh::lean_is_exclusive(v_a_4193_)) as u8;
                    if v_isSharedCheck_4206_ == 0 {
                        v___x_4199_ = v_a_4193_;
                        v_isShared_4200_ = v_isSharedCheck_4206_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4197_);
                        crate::leanh::lean_inc(v_head_4196_);
                        crate::leanh::lean_dec(v_a_4193_);
                        v___x_4199_ = crate::leanh::lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4201_ = l_Lean_mkLevelParam(v_head_4196_);
                if v_isShared_4200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4199_, 1, v_a_4194_);
                    crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4201_);
                    v___x_4203_ = v___x_4199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4205_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_a_4194_);
                    v___x_4203_ = v_reuseFailAlloc_4205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4193_ = v_tail_4197_;
                v_a_4194_ = v___x_4203_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4207_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_4209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_4211_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4212_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4212_, 0, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4212_, 2, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4212_, 3, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4212_, 4, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4212_, 5, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4212_, 6, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4212_, 7, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4212_, 8, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4212_, 9, v___x_4210_);
    return v___x_4212_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4214_ = lean_mk_empty_array_with_capacity(v___x_4213_);
    v___x_4215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4214_);
    return v___x_4215_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4216_: usize = 0;
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = 5usize;
    v___x_4217_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4218_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4219_ = lean_mk_empty_array_with_capacity(v___x_4218_);
    v___x_4220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_4221_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4221_, 0, v___x_4220_);
    crate::leanh::lean_ctor_set(v___x_4221_, 1, v___x_4219_);
    crate::leanh::lean_ctor_set(v___x_4221_, 2, v___x_4217_);
    crate::leanh::lean_ctor_set(v___x_4221_, 3, v___x_4217_);
    crate::leanh::lean_ctor_set_usize(v___x_4221_, 4, v___x_4216_);
    return v___x_4221_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4222_ = crate::leanh::lean_box(1);
    v___x_4223_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_4224_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_4225_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4225_, 0, v___x_4224_);
    crate::leanh::lean_ctor_set(v___x_4225_, 1, v___x_4223_);
    crate::leanh::lean_ctor_set(v___x_4225_, 2, v___x_4222_);
    return v___x_4225_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_4228_ = l_Lean_stringToMessageData(v___x_4227_);
    return v___x_4228_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
    return v___x_4231_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_4234_ = l_Lean_stringToMessageData(v___x_4233_);
    return v___x_4234_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_4237_ = l_Lean_stringToMessageData(v___x_4236_);
    return v___x_4237_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_4240_ = l_Lean_stringToMessageData(v___x_4239_);
    return v___x_4240_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4245_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_4246_ = l_Lean_stringToMessageData(v___x_4245_);
    return v___x_4246_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_msg_4247_: *mut crate::leanh::LeanObject,
    mut v_declHint_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v_isExporting_4254_: u8 = 0;
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: u8 = 0;
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4251_ = lean_st_ref_get(v___y_4249_);
                v_env_4252_ = crate::leanh::lean_ctor_get(v___x_4251_, 0);
                crate::leanh::lean_inc_ref(v_env_4252_);
                crate::leanh::lean_dec(v___x_4251_);
                v___x_4253_ = l_Lean_Name_isAnonymous(v_declHint_4248_);
                if v___x_4253_ == 0 {
                    v_isExporting_4254_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_4252_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4254_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_4252_);
                        crate::leanh::lean_dec(v_declHint_4248_);
                        v___x_4255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4255_, 0, v_msg_4247_);
                        return v___x_4255_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_4252_);
                        v___x_4256_ = l_Lean_Environment_setExporting(v_env_4252_, v___x_4253_);
                        crate::leanh::lean_inc(v_declHint_4248_);
                        crate::leanh::lean_inc_ref(v___x_4256_);
                        v___x_4257_ = l_Lean_Environment_contains(
                            v___x_4256_,
                            v_declHint_4248_,
                            v_isExporting_4254_,
                        );
                        if v___x_4257_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4256_);
                            crate::leanh::lean_dec_ref(v_env_4252_);
                            crate::leanh::lean_dec(v_declHint_4248_);
                            v___x_4258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4258_, 0, v_msg_4247_);
                            return v___x_4258_;
                        } else {
                            v___x_4259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_4260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_4261_ = l_Lean_Options_empty;
                            v___x_4262_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4262_, 0, v___x_4256_);
                            crate::leanh::lean_ctor_set(v___x_4262_, 1, v___x_4259_);
                            crate::leanh::lean_ctor_set(v___x_4262_, 2, v___x_4260_);
                            crate::leanh::lean_ctor_set(v___x_4262_, 3, v___x_4261_);
                            crate::leanh::lean_inc(v_declHint_4248_);
                            v___x_4263_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4248_, v___x_4253_);
                            v_c_4264_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_4264_, 0, v___x_4262_);
                            crate::leanh::lean_ctor_set(v_c_4264_, 1, v___x_4263_);
                            v___x_4265_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4252_,
                                v_declHint_4248_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4265_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_4252_);
                                crate::leanh::lean_dec(v_declHint_4248_);
                                v___x_4266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_4267_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
                                crate::leanh::lean_ctor_set(v___x_4267_, 1, v_c_4264_);
                                v___x_4268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_4269_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4269_, 0, v___x_4267_);
                                crate::leanh::lean_ctor_set(v___x_4269_, 1, v___x_4268_);
                                v___x_4270_ = l_Lean_MessageData_note(v___x_4269_);
                                v___x_4271_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4271_, 0, v_msg_4247_);
                                crate::leanh::lean_ctor_set(v___x_4271_, 1, v___x_4270_);
                                v___x_4272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                                return v___x_4272_;
                            } else {
                                v_val_4273_ = crate::leanh::lean_ctor_get(v___x_4265_, 0);
                                v_isSharedCheck_4308_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4265_)) as u8;
                                if v_isSharedCheck_4308_ == 0 {
                                    v___x_4275_ = v___x_4265_;
                                    v_isShared_4276_ = v_isSharedCheck_4308_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4273_);
                                    crate::leanh::lean_dec(v___x_4265_);
                                    v___x_4275_ = crate::leanh::lean_box(0);
                                    v_isShared_4276_ = v_isSharedCheck_4308_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4252_);
                    crate::leanh::lean_dec(v_declHint_4248_);
                    v___x_4309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4309_, 0, v_msg_4247_);
                    return v___x_4309_;
                }
            }
            1 => {
                v___x_4277_ = crate::leanh::lean_box(0);
                v___x_4278_ = l_Lean_Environment_header(v_env_4252_);
                crate::leanh::lean_dec_ref(v_env_4252_);
                v___x_4279_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4278_);
                v_mod_4280_ = lean_array_get(v___x_4277_, v___x_4279_, v_val_4273_);
                crate::leanh::lean_dec(v_val_4273_);
                crate::leanh::lean_dec_ref(v___x_4279_);
                v___x_4281_ = l_Lean_isPrivateName(v_declHint_4248_);
                crate::leanh::lean_dec(v_declHint_4248_);
                if v___x_4281_ == 0 {
                    v___x_4282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_4283_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4283_, 0, v___x_4282_);
                    crate::leanh::lean_ctor_set(v___x_4283_, 1, v_c_4264_);
                    v___x_4284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_4285_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4285_, 0, v___x_4283_);
                    crate::leanh::lean_ctor_set(v___x_4285_, 1, v___x_4284_);
                    v___x_4286_ = l_Lean_MessageData_ofName(v_mod_4280_);
                    v___x_4287_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4285_);
                    crate::leanh::lean_ctor_set(v___x_4287_, 1, v___x_4286_);
                    v___x_4288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_4289_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4289_, 0, v___x_4287_);
                    crate::leanh::lean_ctor_set(v___x_4289_, 1, v___x_4288_);
                    v___x_4290_ = l_Lean_MessageData_note(v___x_4289_);
                    v___x_4291_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4291_, 0, v_msg_4247_);
                    crate::leanh::lean_ctor_set(v___x_4291_, 1, v___x_4290_);
                    if v_isShared_4276_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4275_, 0);
                        crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4291_);
                        v___x_4293_ = v___x_4275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
                        v___x_4293_ = v_reuseFailAlloc_4294_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_4296_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4296_, 0, v___x_4295_);
                    crate::leanh::lean_ctor_set(v___x_4296_, 1, v_c_4264_);
                    v___x_4297_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_4298_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4298_, 0, v___x_4296_);
                    crate::leanh::lean_ctor_set(v___x_4298_, 1, v___x_4297_);
                    v___x_4299_ = l_Lean_MessageData_ofName(v_mod_4280_);
                    v___x_4300_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4298_);
                    crate::leanh::lean_ctor_set(v___x_4300_, 1, v___x_4299_);
                    v___x_4301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_4302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4302_, 0, v___x_4300_);
                    crate::leanh::lean_ctor_set(v___x_4302_, 1, v___x_4301_);
                    v___x_4303_ = l_Lean_MessageData_note(v___x_4302_);
                    v___x_4304_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4304_, 0, v_msg_4247_);
                    crate::leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
                    if v_isShared_4276_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4275_, 0);
                        crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4304_);
                        v___x_4306_ = v___x_4275_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4293_;
            }
            3 => {
                return v___x_4306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_4310_: *mut crate::leanh::LeanObject,
    mut v_declHint_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4310_, v_declHint_4311_, v___y_4312_);
    crate::leanh::lean_dec(v___y_4312_);
    return v_res_4314_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(
    mut v_msg_4315_: *mut crate::leanh::LeanObject,
    mut v_declHint_4316_: *mut crate::leanh::LeanObject,
    mut v___y_4317_: *mut crate::leanh::LeanObject,
    mut v___y_4318_: *mut crate::leanh::LeanObject,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4315_, v_declHint_4316_, v___y_4320_);
                v_a_4323_ = crate::leanh::lean_ctor_get(v___x_4322_, 0);
                v_isSharedCheck_4332_ = (!crate::leanh::lean_is_exclusive(v___x_4322_)) as u8;
                if v_isSharedCheck_4332_ == 0 {
                    v___x_4325_ = v___x_4322_;
                    v_isShared_4326_ = v_isSharedCheck_4332_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4323_);
                    crate::leanh::lean_dec(v___x_4322_);
                    v___x_4325_ = crate::leanh::lean_box(0);
                    v_isShared_4326_ = v_isSharedCheck_4332_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4327_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4328_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4328_, 0, v___x_4327_);
                crate::leanh::lean_ctor_set(v___x_4328_, 1, v_a_4323_);
                if v_isShared_4326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(
    mut v_msg_4333_: *mut crate::leanh::LeanObject,
    mut v_declHint_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_4333_, v_declHint_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
    crate::leanh::lean_dec(v___y_4338_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    crate::leanh::lean_dec(v___y_4336_);
    crate::leanh::lean_dec_ref(v___y_4335_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_ref_4341_: *mut crate::leanh::LeanObject,
    mut v_msg_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4360_: u8 = 0;
    let mut v_cancelTk_x3f_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4362_: u8 = 0;
    let mut v_inheritedTraceOptions_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4348_ = crate::leanh::lean_ctor_get(v___y_4345_, 0);
    v_fileMap_4349_ = crate::leanh::lean_ctor_get(v___y_4345_, 1);
    v_options_4350_ = crate::leanh::lean_ctor_get(v___y_4345_, 2);
    v_currRecDepth_4351_ = crate::leanh::lean_ctor_get(v___y_4345_, 3);
    v_maxRecDepth_4352_ = crate::leanh::lean_ctor_get(v___y_4345_, 4);
    v_ref_4353_ = crate::leanh::lean_ctor_get(v___y_4345_, 5);
    v_currNamespace_4354_ = crate::leanh::lean_ctor_get(v___y_4345_, 6);
    v_openDecls_4355_ = crate::leanh::lean_ctor_get(v___y_4345_, 7);
    v_initHeartbeats_4356_ = crate::leanh::lean_ctor_get(v___y_4345_, 8);
    v_maxHeartbeats_4357_ = crate::leanh::lean_ctor_get(v___y_4345_, 9);
    v_quotContext_4358_ = crate::leanh::lean_ctor_get(v___y_4345_, 10);
    v_currMacroScope_4359_ = crate::leanh::lean_ctor_get(v___y_4345_, 11);
    v_diag_4360_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4361_ = crate::leanh::lean_ctor_get(v___y_4345_, 12);
    v_suppressElabErrors_4362_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4363_ = crate::leanh::lean_ctor_get(v___y_4345_, 13);
    v_ref_4364_ = l_Lean_replaceRef(v_ref_4341_, v_ref_4353_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4363_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4361_);
    crate::leanh::lean_inc(v_currMacroScope_4359_);
    crate::leanh::lean_inc(v_quotContext_4358_);
    crate::leanh::lean_inc(v_maxHeartbeats_4357_);
    crate::leanh::lean_inc(v_initHeartbeats_4356_);
    crate::leanh::lean_inc(v_openDecls_4355_);
    crate::leanh::lean_inc(v_currNamespace_4354_);
    crate::leanh::lean_inc(v_maxRecDepth_4352_);
    crate::leanh::lean_inc(v_currRecDepth_4351_);
    crate::leanh::lean_inc_ref(v_options_4350_);
    crate::leanh::lean_inc_ref(v_fileMap_4349_);
    crate::leanh::lean_inc_ref(v_fileName_4348_);
    v___x_4365_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4365_, 0, v_fileName_4348_);
    crate::leanh::lean_ctor_set(v___x_4365_, 1, v_fileMap_4349_);
    crate::leanh::lean_ctor_set(v___x_4365_, 2, v_options_4350_);
    crate::leanh::lean_ctor_set(v___x_4365_, 3, v_currRecDepth_4351_);
    crate::leanh::lean_ctor_set(v___x_4365_, 4, v_maxRecDepth_4352_);
    crate::leanh::lean_ctor_set(v___x_4365_, 5, v_ref_4364_);
    crate::leanh::lean_ctor_set(v___x_4365_, 6, v_currNamespace_4354_);
    crate::leanh::lean_ctor_set(v___x_4365_, 7, v_openDecls_4355_);
    crate::leanh::lean_ctor_set(v___x_4365_, 8, v_initHeartbeats_4356_);
    crate::leanh::lean_ctor_set(v___x_4365_, 9, v_maxHeartbeats_4357_);
    crate::leanh::lean_ctor_set(v___x_4365_, 10, v_quotContext_4358_);
    crate::leanh::lean_ctor_set(v___x_4365_, 11, v_currMacroScope_4359_);
    crate::leanh::lean_ctor_set(v___x_4365_, 12, v_cancelTk_x3f_4361_);
    crate::leanh::lean_ctor_set(v___x_4365_, 13, v_inheritedTraceOptions_4363_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4365_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4360_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4365_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4362_,
    );
    v___x_4366_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(
        v_msg_4342_,
        v___y_4343_,
        v___y_4344_,
        v___x_4365_,
        v___y_4346_,
    );
    crate::leanh::lean_dec_ref_known(v___x_4365_, 14);
    return v___x_4366_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_ref_4367_: *mut crate::leanh::LeanObject,
    mut v_msg_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
    mut v___y_4371_: *mut crate::leanh::LeanObject,
    mut v___y_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4374_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4367_, v_msg_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
    crate::leanh::lean_dec(v___y_4372_);
    crate::leanh::lean_dec_ref(v___y_4371_);
    crate::leanh::lean_dec(v___y_4370_);
    crate::leanh::lean_dec_ref(v___y_4369_);
    crate::leanh::lean_dec(v_ref_4367_);
    return v_res_4374_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_4375_: *mut crate::leanh::LeanObject,
    mut v_msg_4376_: *mut crate::leanh::LeanObject,
    mut v_declHint_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
    mut v___y_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4383_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_4376_, v_declHint_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
    v_a_4384_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
    crate::leanh::lean_inc(v_a_4384_);
    crate::leanh::lean_dec_ref(v___x_4383_);
    v___x_4385_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4375_, v_a_4384_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
    return v___x_4385_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_4386_: *mut crate::leanh::LeanObject,
    mut v_msg_4387_: *mut crate::leanh::LeanObject,
    mut v_declHint_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4386_, v_msg_4387_, v_declHint_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
    crate::leanh::lean_dec(v___y_4392_);
    crate::leanh::lean_dec_ref(v___y_4391_);
    crate::leanh::lean_dec(v___y_4390_);
    crate::leanh::lean_dec_ref(v___y_4389_);
    crate::leanh::lean_dec(v_ref_4386_);
    return v_res_4394_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4398_: *mut crate::leanh::LeanObject,
    mut v_constName_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4406_ = 0;
    crate::leanh::lean_inc(v_constName_4399_);
    v___x_4407_ = l_Lean_MessageData_ofConstName(v_constName_4399_, v___x_4406_);
    v___x_4408_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4405_);
    crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4407_);
    v___x_4409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1,
    );
    v___x_4410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4408_);
    crate::leanh::lean_ctor_set(v___x_4410_, 1, v___x_4409_);
    v___x_4411_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4398_, v___x_4410_, v_constName_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
    return v___x_4411_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4412_: *mut crate::leanh::LeanObject,
    mut v_constName_4413_: *mut crate::leanh::LeanObject,
    mut v___y_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4419_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_4412_, v_constName_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
    crate::leanh::lean_dec(v___y_4417_);
    crate::leanh::lean_dec_ref(v___y_4416_);
    crate::leanh::lean_dec(v___y_4415_);
    crate::leanh::lean_dec_ref(v___y_4414_);
    crate::leanh::lean_dec(v_ref_4412_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(
    mut v_constName_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4426_ = crate::leanh::lean_ctor_get(v___y_4423_, 5);
    v___x_4427_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_4426_, v_constName_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
    return v___x_4427_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(
    mut v_constName_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4434_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
    crate::leanh::lean_dec(v___y_4432_);
    crate::leanh::lean_dec_ref(v___y_4431_);
    crate::leanh::lean_dec(v___y_4430_);
    crate::leanh::lean_dec_ref(v___y_4429_);
    return v_res_4434_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(
    mut v_constName_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4441_ = lean_st_ref_get(v___y_4439_);
                v_env_4442_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                crate::leanh::lean_inc_ref(v_env_4442_);
                crate::leanh::lean_dec(v___x_4441_);
                v___x_4443_ = 0;
                crate::leanh::lean_inc(v_constName_4435_);
                v___x_4444_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4442_,
                    v_constName_4435_,
                    v___x_4443_,
                );
                if crate::leanh::lean_obj_tag(v___x_4444_) == 0 {
                    v___x_4445_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
                    return v___x_4445_;
                } else {
                    crate::leanh::lean_dec(v_constName_4435_);
                    v_val_4446_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                    v_isSharedCheck_4453_ = (!crate::leanh::lean_is_exclusive(v___x_4444_)) as u8;
                    if v_isSharedCheck_4453_ == 0 {
                        v___x_4448_ = v___x_4444_;
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4446_);
                        crate::leanh::lean_dec(v___x_4444_);
                        v___x_4448_ = crate::leanh::lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4448_, 0);
                    v___x_4451_ = v___x_4448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_val_4446_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(
    mut v_constName_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(
        v_constName_4454_,
        v___y_4455_,
        v___y_4456_,
        v___y_4457_,
        v___y_4458_,
    );
    crate::leanh::lean_dec(v___y_4458_);
    crate::leanh::lean_dec_ref(v___y_4457_);
    crate::leanh::lean_dec(v___y_4456_);
    crate::leanh::lean_dec_ref(v___y_4455_);
    return v_res_4460_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofForDecl___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4462_ = l_Lean_Meta_Grind_getProofForDecl___closed__0;
    v___x_4463_ = l_Lean_stringToMessageData(v___x_4462_);
    return v___x_4463_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getProofForDecl___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ = l_Lean_Meta_Grind_getProofForDecl___closed__2;
    v___x_4466_ = l_Lean_stringToMessageData(v___x_4465_);
    return v___x_4466_;
}
pub unsafe fn l_Lean_Meta_Grind_getProofForDecl(
    mut v_declName_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v_levelParams_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: u8 = 0;
    let mut v_type_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4503_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v_a_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut v_a_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4520_: u8 = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_4467_);
                v___x_4473_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(
                    v_declName_4467_,
                    v_a_4468_,
                    v_a_4469_,
                    v_a_4470_,
                    v_a_4471_,
                );
                if crate::leanh::lean_obj_tag(v___x_4473_) == 0 {
                    v_a_4474_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4516_ = (!crate::leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4516_ == 0 {
                        v___x_4476_ = v___x_4473_;
                        v_isShared_4477_ = v_isSharedCheck_4516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4474_);
                        crate::leanh::lean_dec(v___x_4473_);
                        v___x_4476_ = crate::leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4516_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_4467_);
                    v_a_4517_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4524_ = (!crate::leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4524_ == 0 {
                        v___x_4519_ = v___x_4473_;
                        v_isShared_4520_ = v_isSharedCheck_4524_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4517_);
                        crate::leanh::lean_dec(v___x_4473_);
                        v___x_4519_ = crate::leanh::lean_box(0);
                        v_isShared_4520_ = v_isSharedCheck_4524_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4486_ = lean_st_ref_get(v_a_4471_);
                v_env_4487_ = crate::leanh::lean_ctor_get(v___x_4486_, 0);
                crate::leanh::lean_inc_ref(v_env_4487_);
                crate::leanh::lean_dec(v___x_4486_);
                crate::leanh::lean_inc(v_declName_4467_);
                v___x_4488_ = l_Lean_wasOriginallyTheorem(v_env_4487_, v_declName_4467_);
                if v___x_4488_ == 0 {
                    v_type_4489_ = crate::leanh::lean_ctor_get(v_a_4474_, 2);
                    crate::leanh::lean_inc_ref(v_type_4489_);
                    v___x_4490_ = l_Lean_Meta_isProp(
                        v_type_4489_,
                        v_a_4468_,
                        v_a_4469_,
                        v_a_4470_,
                        v_a_4471_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4490_) == 0 {
                        v_a_4491_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                        crate::leanh::lean_inc(v_a_4491_);
                        crate::leanh::lean_dec_ref_known(v___x_4490_, 1);
                        v___x_4492_ = (crate::leanh::lean_unbox(v_a_4491_) as u8);
                        if v___x_4492_ == 0 {
                            crate::leanh::lean_del_object(v___x_4476_);
                            crate::leanh::lean_dec(v_a_4474_);
                            v___x_4493_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getProofForDecl___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getProofForDecl___closed__1_once
                                ),
                                _init_l_Lean_Meta_Grind_getProofForDecl___closed__1,
                            );
                            v___x_4494_ = (crate::leanh::lean_unbox(v_a_4491_) as u8);
                            crate::leanh::lean_dec(v_a_4491_);
                            v___x_4495_ =
                                l_Lean_MessageData_ofConstName(v_declName_4467_, v___x_4494_);
                            v___x_4496_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4496_, 0, v___x_4493_);
                            crate::leanh::lean_ctor_set(v___x_4496_, 1, v___x_4495_);
                            v___x_4497_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getProofForDecl___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getProofForDecl___closed__3_once
                                ),
                                _init_l_Lean_Meta_Grind_getProofForDecl___closed__3,
                            );
                            v___x_4498_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4498_, 0, v___x_4496_);
                            crate::leanh::lean_ctor_set(v___x_4498_, 1, v___x_4497_);
                            v___x_4499_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_4498_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
                            v_a_4500_ = crate::leanh::lean_ctor_get(v___x_4499_, 0);
                            v_isSharedCheck_4507_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4499_)) as u8;
                            if v_isSharedCheck_4507_ == 0 {
                                v___x_4502_ = v___x_4499_;
                                v_isShared_4503_ = v_isSharedCheck_4507_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4500_);
                                crate::leanh::lean_dec(v___x_4499_);
                                v___x_4502_ = crate::leanh::lean_box(0);
                                v_isShared_4503_ = v_isSharedCheck_4507_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4491_);
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4476_);
                        crate::leanh::lean_dec(v_a_4474_);
                        crate::leanh::lean_dec(v_declName_4467_);
                        v_a_4508_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                        v_isSharedCheck_4515_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4490_)) as u8;
                        if v_isSharedCheck_4515_ == 0 {
                            v___x_4510_ = v___x_4490_;
                            v_isShared_4511_ = v_isSharedCheck_4515_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4508_);
                            crate::leanh::lean_dec(v___x_4490_);
                            v___x_4510_ = crate::leanh::lean_box(0);
                            v_isShared_4511_ = v_isSharedCheck_4515_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_levelParams_4479_ = crate::leanh::lean_ctor_get(v_a_4474_, 1);
                crate::leanh::lean_inc(v_levelParams_4479_);
                crate::leanh::lean_dec(v_a_4474_);
                v___x_4480_ = crate::leanh::lean_box(0);
                v___x_4481_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(
                    v_levelParams_4479_,
                    v___x_4480_,
                );
                v___x_4482_ = l_Lean_mkConst(v_declName_4467_, v___x_4481_);
                if v_isShared_4477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4476_, 0, v___x_4482_);
                    v___x_4484_ = v___x_4476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
                    v___x_4484_ = v_reuseFailAlloc_4485_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4484_;
            }
            4 => {
                if v_isShared_4503_ == 0 {
                    v___x_4505_ = v___x_4502_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
                    v___x_4505_ = v_reuseFailAlloc_4506_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4505_;
            }
            6 => {
                if v_isShared_4511_ == 0 {
                    v___x_4513_ = v___x_4510_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
                    v___x_4513_ = v_reuseFailAlloc_4514_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4513_;
            }
            8 => {
                if v_isShared_4520_ == 0 {
                    v___x_4522_ = v___x_4519_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
                    v___x_4522_ = v_reuseFailAlloc_4523_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getProofForDecl___boxed(
    mut v_declName_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ = l_Lean_Meta_Grind_getProofForDecl(
        v_declName_4525_,
        v_a_4526_,
        v_a_4527_,
        v_a_4528_,
        v_a_4529_,
    );
    crate::leanh::lean_dec(v_a_4529_);
    crate::leanh::lean_dec_ref(v_a_4528_);
    crate::leanh::lean_dec(v_a_4527_);
    crate::leanh::lean_dec_ref(v_a_4526_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(
    mut v_00_u03b1_4532_: *mut crate::leanh::LeanObject,
    mut v_constName_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4539_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
    return v___x_4539_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(
    mut v_00_u03b1_4540_: *mut crate::leanh::LeanObject,
    mut v_constName_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(v_00_u03b1_4540_, v_constName_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
    crate::leanh::lean_dec(v___y_4545_);
    crate::leanh::lean_dec_ref(v___y_4544_);
    crate::leanh::lean_dec(v___y_4543_);
    crate::leanh::lean_dec_ref(v___y_4542_);
    return v_res_4547_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4548_: *mut crate::leanh::LeanObject,
    mut v_ref_4549_: *mut crate::leanh::LeanObject,
    mut v_constName_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_4549_, v_constName_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4557_: *mut crate::leanh::LeanObject,
    mut v_ref_4558_: *mut crate::leanh::LeanObject,
    mut v_constName_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4565_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(v_00_u03b1_4557_, v_ref_4558_, v_constName_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
    crate::leanh::lean_dec(v___y_4563_);
    crate::leanh::lean_dec_ref(v___y_4562_);
    crate::leanh::lean_dec(v___y_4561_);
    crate::leanh::lean_dec_ref(v___y_4560_);
    crate::leanh::lean_dec(v_ref_4558_);
    return v_res_4565_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_4566_: *mut crate::leanh::LeanObject,
    mut v_ref_4567_: *mut crate::leanh::LeanObject,
    mut v_msg_4568_: *mut crate::leanh::LeanObject,
    mut v_declHint_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4567_, v_msg_4568_, v_declHint_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
    return v___x_4575_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_4576_: *mut crate::leanh::LeanObject,
    mut v_ref_4577_: *mut crate::leanh::LeanObject,
    mut v_msg_4578_: *mut crate::leanh::LeanObject,
    mut v_declHint_4579_: *mut crate::leanh::LeanObject,
    mut v___y_4580_: *mut crate::leanh::LeanObject,
    mut v___y_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4576_, v_ref_4577_, v_msg_4578_, v_declHint_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
    crate::leanh::lean_dec(v___y_4583_);
    crate::leanh::lean_dec_ref(v___y_4582_);
    crate::leanh::lean_dec(v___y_4581_);
    crate::leanh::lean_dec_ref(v___y_4580_);
    crate::leanh::lean_dec(v_ref_4577_);
    return v_res_4585_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_msg_4586_: *mut crate::leanh::LeanObject,
    mut v_declHint_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4593_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4586_, v_declHint_4587_, v___y_4591_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4594_: *mut crate::leanh::LeanObject,
    mut v_declHint_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4601_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_4594_, v_declHint_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
    crate::leanh::lean_dec(v___y_4599_);
    crate::leanh::lean_dec_ref(v___y_4598_);
    crate::leanh::lean_dec(v___y_4597_);
    crate::leanh::lean_dec_ref(v___y_4596_);
    return v_res_4601_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b1_4602_: *mut crate::leanh::LeanObject,
    mut v_ref_4603_: *mut crate::leanh::LeanObject,
    mut v_msg_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4603_, v_msg_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
    return v___x_4610_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b1_4611_: *mut crate::leanh::LeanObject,
    mut v_ref_4612_: *mut crate::leanh::LeanObject,
    mut v_msg_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4611_, v_ref_4612_, v_msg_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
    crate::leanh::lean_dec(v___y_4617_);
    crate::leanh::lean_dec_ref(v___y_4616_);
    crate::leanh::lean_dec(v___y_4615_);
    crate::leanh::lean_dec_ref(v___y_4614_);
    crate::leanh::lean_dec(v_ref_4612_);
    return v_res_4619_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(
    mut v___x_4620_: *mut crate::leanh::LeanObject,
    mut v_s_4621_: *mut crate::leanh::LeanObject,
    mut v_sym_4622_: *mut crate::leanh::LeanObject,
    mut v___x_4623_: *mut crate::leanh::LeanObject,
    mut v___x_4624_: *mut crate::leanh::LeanObject,
    mut v_next_4625_: *mut crate::leanh::LeanObject,
    mut v_acc_4626_: *mut crate::leanh::LeanObject,
    mut v_h_4627_: *mut crate::leanh::LeanObject,
    mut v_G_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_smap_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origins_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omap_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4644_: u8 = 0;
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4629_ = lean_nat_dec_lt(v_next_4625_, v___x_4620_);
                if v___x_4629_ == 0 {
                    crate::leanh::lean_dec_ref(v_G_4628_);
                    crate::leanh::lean_dec_ref(v___x_4624_);
                    crate::leanh::lean_dec(v_sym_4622_);
                    crate::leanh::lean_dec_ref(v_s_4621_);
                    crate::leanh::lean_inc_ref(v_acc_4626_);
                    return v_acc_4626_;
                } else {
                    v___x_4630_ = lean_array_fget(v_s_4621_, v_next_4625_);
                    v_smap_4631_ = crate::leanh::lean_ctor_get(v___x_4630_, 0);
                    v_origins_4632_ = crate::leanh::lean_ctor_get(v___x_4630_, 1);
                    v_erased_4633_ = crate::leanh::lean_ctor_get(v___x_4630_, 2);
                    v_omap_4634_ = crate::leanh::lean_ctor_get(v___x_4630_, 3);
                    v_isSharedCheck_4660_ = (!crate::leanh::lean_is_exclusive(v___x_4630_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4636_ = v___x_4630_;
                        v_isShared_4637_ = v_isSharedCheck_4660_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_omap_4634_);
                        crate::leanh::lean_inc(v_erased_4633_);
                        crate::leanh::lean_inc(v_origins_4632_);
                        crate::leanh::lean_inc(v_smap_4631_);
                        crate::leanh::lean_dec(v___x_4630_);
                        v___x_4636_ = crate::leanh::lean_box(0);
                        v_isShared_4637_ = v_isSharedCheck_4660_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4638_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15;
                v___x_4639_ = l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16;
                crate::leanh::lean_inc(v_sym_4622_);
                v___x_4640_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_4638_,
                    v___x_4639_,
                    v_smap_4631_,
                    v_sym_4622_,
                );
                if crate::leanh::lean_obj_tag(v___x_4640_) == 1 {
                    crate::leanh::lean_dec_ref(v_G_4628_);
                    crate::leanh::lean_dec_ref(v___x_4624_);
                    v_val_4641_ = crate::leanh::lean_ctor_get(v___x_4640_, 0);
                    v_isSharedCheck_4656_ = (!crate::leanh::lean_is_exclusive(v___x_4640_)) as u8;
                    if v_isSharedCheck_4656_ == 0 {
                        v___x_4643_ = v___x_4640_;
                        v_isShared_4644_ = v_isSharedCheck_4656_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4641_);
                        crate::leanh::lean_dec(v___x_4640_);
                        v___x_4643_ = crate::leanh::lean_box(0);
                        v_isShared_4644_ = v_isSharedCheck_4656_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4640_);
                    crate::leanh::lean_del_object(v___x_4636_);
                    crate::leanh::lean_dec_ref(v_omap_4634_);
                    crate::leanh::lean_dec_ref(v_erased_4633_);
                    crate::leanh::lean_dec_ref(v_origins_4632_);
                    crate::leanh::lean_dec_ref(v_smap_4631_);
                    crate::leanh::lean_dec(v_sym_4622_);
                    crate::leanh::lean_dec_ref(v_s_4621_);
                    v___x_4657_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4658_ = lean_nat_add(v_next_4625_, v___x_4657_);
                    v___x_4659_ = crate::leanh::lean_apply_4(
                        v_G_4628_,
                        v___x_4658_,
                        v___x_4624_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4659_;
                }
            }
            2 => {
                v___x_4645_ = l_Lean_PersistentHashMap_erase___redArg(
                    v___x_4638_,
                    v___x_4639_,
                    v_smap_4631_,
                    v_sym_4622_,
                );
                if v_isShared_4637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4636_, 0, v___x_4645_);
                    v___x_4647_ = v___x_4636_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_origins_4632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 2, v_erased_4633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 3, v_omap_4634_);
                    v___x_4647_ = v_reuseFailAlloc_4655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4648_ = lean_array_fset(v_s_4621_, v_next_4625_, v___x_4647_);
                v___x_4649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4649_, 0, v_val_4641_);
                crate::leanh::lean_ctor_set(v___x_4649_, 1, v___x_4648_);
                if v_isShared_4644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4643_, 0, v___x_4649_);
                    v___x_4651_ = v___x_4643_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4649_);
                    v___x_4651_ = v_reuseFailAlloc_4654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4652_, 0, v___x_4651_);
                v___x_4653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4653_, 0, v___x_4652_);
                crate::leanh::lean_ctor_set(v___x_4653_, 1, v___x_4623_);
                return v___x_4653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(
    mut v___x_4661_: *mut crate::leanh::LeanObject,
    mut v_s_4662_: *mut crate::leanh::LeanObject,
    mut v_sym_4663_: *mut crate::leanh::LeanObject,
    mut v___x_4664_: *mut crate::leanh::LeanObject,
    mut v___x_4665_: *mut crate::leanh::LeanObject,
    mut v_next_4666_: *mut crate::leanh::LeanObject,
    mut v_acc_4667_: *mut crate::leanh::LeanObject,
    mut v_h_4668_: *mut crate::leanh::LeanObject,
    mut v_G_4669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4670_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(
        v___x_4661_,
        v_s_4662_,
        v_sym_4663_,
        v___x_4664_,
        v___x_4665_,
        v_next_4666_,
        v_acc_4667_,
        v_h_4668_,
        v_G_4669_,
    );
    crate::leanh::lean_dec_ref(v_acc_4667_);
    crate::leanh::lean_dec(v_next_4666_);
    crate::leanh::lean_dec(v___x_4661_);
    return v_res_4670_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(
    mut v_s_4674_: *mut crate::leanh::LeanObject,
    mut v_sym_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ = lean_array_get_size(v_s_4674_);
    v___x_4677_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4678_ = crate::leanh::lean_box(0);
    v___x_4679_ = crate::leanh::lean_box(0);
    v___x_4680_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0;
    v___f_4681_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4681_, 0, v___x_4676_);
    crate::leanh::lean_closure_set(v___f_4681_, 1, v_s_4674_);
    crate::leanh::lean_closure_set(v___f_4681_, 2, v_sym_4675_);
    crate::leanh::lean_closure_set(v___f_4681_, 3, v___x_4679_);
    crate::leanh::lean_closure_set(v___f_4681_, 4, v___x_4680_);
    v___x_4682_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_4681_,
        v___x_4677_,
        v___x_4680_,
        crate::leanh::lean_box(0),
    );
    v_fst_4683_ = crate::leanh::lean_ctor_get(v___x_4682_, 0);
    crate::leanh::lean_inc(v_fst_4683_);
    crate::leanh::lean_dec(v___x_4682_);
    if crate::leanh::lean_obj_tag(v_fst_4683_) == 0 {
        return v___x_4678_;
    } else {
        let mut v_val_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4684_ = crate::leanh::lean_ctor_get(v_fst_4683_, 0);
        crate::leanh::lean_inc(v_val_4684_);
        crate::leanh::lean_dec_ref_known(v_fst_4683_, 1);
        return v_val_4684_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(
    mut v_00_u03b1_4685_: *mut crate::leanh::LeanObject,
    mut v_s_4686_: *mut crate::leanh::LeanObject,
    mut v_sym_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(v_s_4686_, v_sym_4687_);
    return v___x_4688_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4689_ = l_Lean_Meta_Grind_instHashableOrigin___closed__0;
    v___f_4690_ = l_Lean_Meta_Grind_instBEqOrigin___closed__0;
    v___x_4691_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_4690_,
        v___f_4689_,
    );
    return v___x_4691_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once),
        _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0,
    );
    v___x_4693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once),
        _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1,
    );
    v_thms_4694_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v_thms_4694_, 0, v___x_4693_);
    crate::leanh::lean_ctor_set(v_thms_4694_, 1, v___x_4692_);
    crate::leanh::lean_ctor_set(v_thms_4694_, 2, v___x_4692_);
    crate::leanh::lean_ctor_set(v_thms_4694_, 3, v___x_4693_);
    return v_thms_4694_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_insert___redArg(
    mut v_inst_4695_: *mut crate::leanh::LeanObject,
    mut v_s_4696_: *mut crate::leanh::LeanObject,
    mut v_thm_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    v___x_4698_ = lean_array_get_size(v_s_4696_);
    v___x_4699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4700_ = lean_nat_dec_eq(v___x_4698_, v___x_4699_);
    if v___x_4700_ == 0 {
        let mut v___x_4701_: u8 = 0;
        v___x_4701_ = lean_nat_dec_lt(v___x_4699_, v___x_4698_);
        if v___x_4701_ == 0 {
            crate::leanh::lean_dec(v_thm_4697_);
            crate::leanh::lean_dec_ref(v_inst_4695_);
            return v_s_4696_;
        } else {
            let mut v_v_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_xs_x27_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_4702_ = lean_array_fget(v_s_4696_, v___x_4699_);
            v___x_4703_ = crate::leanh::lean_box(0);
            v_xs_x27_4704_ = lean_array_fset(v_s_4696_, v___x_4699_, v___x_4703_);
            v___x_4705_ =
                l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_4695_, v_v_4702_, v_thm_4697_);
            v___x_4706_ = lean_array_fset(v_xs_x27_4704_, v___x_4699_, v___x_4705_);
            return v___x_4706_;
        }
    } else {
        let mut v_thms_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_4696_);
        v_thms_4707_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once
            ),
            _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1,
        );
        v___x_4708_ =
            l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_4695_, v_thms_4707_, v_thm_4697_);
        v___x_4709_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4710_ = lean_mk_empty_array_with_capacity(v___x_4709_);
        v___x_4711_ = lean_array_push(v___x_4710_, v___x_4708_);
        return v___x_4711_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_insert(
    mut v_00_u03b1_4712_: *mut crate::leanh::LeanObject,
    mut v_inst_4713_: *mut crate::leanh::LeanObject,
    mut v_s_4714_: *mut crate::leanh::LeanObject,
    mut v_thm_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4716_ =
        l_Lean_Meta_Grind_TheoremsArray_insert___redArg(v_inst_4713_, v_s_4714_, v_thm_4715_);
    return v___x_4716_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(
    mut v_origin_4717_: *mut crate::leanh::LeanObject,
    mut v_as_4718_: *mut crate::leanh::LeanObject,
    mut v_i_4719_: usize,
    mut v_stop_4720_: usize,
) -> u8 {
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: usize = 0;
    let mut v___x_4726_: usize = 0;
    let mut v___x_4728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4721_ = lean_usize_dec_eq(v_i_4719_, v_stop_4720_);
                if v___x_4721_ == 0 {
                    v___x_4722_ = lean_array_uget_borrowed(v_as_4718_, v_i_4719_);
                    v_erased_4723_ = crate::leanh::lean_ctor_get(v___x_4722_, 2);
                    v___x_4724_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_4723_, v_origin_4717_);
                    if v___x_4724_ == 0 {
                        v___x_4725_ = 1usize;
                        v___x_4726_ = lean_usize_add(v_i_4719_, v___x_4725_);
                        v_i_4719_ = v___x_4726_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4724_;
                    }
                } else {
                    v___x_4728_ = 0;
                    return v___x_4728_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(
    mut v_origin_4729_: *mut crate::leanh::LeanObject,
    mut v_as_4730_: *mut crate::leanh::LeanObject,
    mut v_i_4731_: *mut crate::leanh::LeanObject,
    mut v_stop_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4733_: usize = 0;
    let mut v_stop_boxed_4734_: usize = 0;
    let mut v_res_4735_: u8 = 0;
    let mut v_r_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4733_ = crate::leanh::lean_unbox_usize(v_i_4731_);
    crate::leanh::lean_dec(v_i_4731_);
    v_stop_boxed_4734_ = crate::leanh::lean_unbox_usize(v_stop_4732_);
    crate::leanh::lean_dec(v_stop_4732_);
    v_res_4735_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_4729_, v_as_4730_, v_i_boxed_4733_, v_stop_boxed_4734_);
    crate::leanh::lean_dec_ref(v_as_4730_);
    crate::leanh::lean_dec_ref(v_origin_4729_);
    v_r_4736_ = crate::leanh::lean_box((v_res_4735_) as usize);
    return v_r_4736_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(
    mut v_s_4737_: *mut crate::leanh::LeanObject,
    mut v_origin_4738_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: u8 = 0;
    v___x_4739_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4740_ = lean_array_get_size(v_s_4737_);
    v___x_4741_ = lean_nat_dec_lt(v___x_4739_, v___x_4740_);
    if v___x_4741_ == 0 {
        return v___x_4741_;
    } else {
        if v___x_4741_ == 0 {
            return v___x_4741_;
        } else {
            let mut v___x_4742_: usize = 0;
            let mut v___x_4743_: usize = 0;
            let mut v___x_4744_: u8 = 0;
            v___x_4742_ = 0usize;
            v___x_4743_ = lean_usize_of_nat(v___x_4740_);
            v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_4738_, v_s_4737_, v___x_4742_, v___x_4743_);
            return v___x_4744_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(
    mut v_s_4745_: *mut crate::leanh::LeanObject,
    mut v_origin_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4747_: u8 = 0;
    let mut v_r_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4747_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_4745_, v_origin_4746_);
    crate::leanh::lean_dec_ref(v_origin_4746_);
    crate::leanh::lean_dec_ref(v_s_4745_);
    v_r_4748_ = crate::leanh::lean_box((v_res_4747_) as usize);
    return v_r_4748_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_isErased(
    mut v_00_u03b1_4749_: *mut crate::leanh::LeanObject,
    mut v_s_4750_: *mut crate::leanh::LeanObject,
    mut v_origin_4751_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4752_: u8 = 0;
    v___x_4752_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_4750_, v_origin_4751_);
    return v___x_4752_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(
    mut v_00_u03b1_4753_: *mut crate::leanh::LeanObject,
    mut v_s_4754_: *mut crate::leanh::LeanObject,
    mut v_origin_4755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4756_: u8 = 0;
    let mut v_r_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4756_ =
        l_Lean_Meta_Grind_TheoremsArray_isErased(v_00_u03b1_4753_, v_s_4754_, v_origin_4755_);
    crate::leanh::lean_dec_ref(v_origin_4755_);
    crate::leanh::lean_dec_ref(v_s_4754_);
    v_r_4757_ = crate::leanh::lean_box((v_res_4756_) as usize);
    return v_r_4757_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(
    mut v_00_u03b1_4758_: *mut crate::leanh::LeanObject,
    mut v_origin_4759_: *mut crate::leanh::LeanObject,
    mut v_as_4760_: *mut crate::leanh::LeanObject,
    mut v_i_4761_: usize,
    mut v_stop_4762_: usize,
) -> u8 {
    let mut v___x_4763_: u8 = 0;
    v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_4759_, v_as_4760_, v_i_4761_, v_stop_4762_);
    return v___x_4763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(
    mut v_00_u03b1_4764_: *mut crate::leanh::LeanObject,
    mut v_origin_4765_: *mut crate::leanh::LeanObject,
    mut v_as_4766_: *mut crate::leanh::LeanObject,
    mut v_i_4767_: *mut crate::leanh::LeanObject,
    mut v_stop_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4769_: usize = 0;
    let mut v_stop_boxed_4770_: usize = 0;
    let mut v_res_4771_: u8 = 0;
    let mut v_r_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4769_ = crate::leanh::lean_unbox_usize(v_i_4767_);
    crate::leanh::lean_dec(v_i_4767_);
    v_stop_boxed_4770_ = crate::leanh::lean_unbox_usize(v_stop_4768_);
    crate::leanh::lean_dec(v_stop_4768_);
    v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(v_00_u03b1_4764_, v_origin_4765_, v_as_4766_, v_i_boxed_4769_, v_stop_boxed_4770_);
    crate::leanh::lean_dec_ref(v_as_4766_);
    crate::leanh::lean_dec_ref(v_origin_4765_);
    v_r_4772_ = crate::leanh::lean_box((v_res_4771_) as usize);
    return v_r_4772_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(
    mut v_upperBound_4773_: *mut crate::leanh::LeanObject,
    mut v_s_4774_: *mut crate::leanh::LeanObject,
    mut v_origin_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_b_4777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4783_ = lean_nat_dec_lt(v_a_4776_, v_upperBound_4773_);
                if v___x_4783_ == 0 {
                    crate::leanh::lean_dec(v_a_4776_);
                    return v_b_4777_;
                } else {
                    v___x_4784_ = lean_array_fget_borrowed(v_s_4774_, v_a_4776_);
                    v___x_4785_ =
                        l_Lean_Meta_Grind_Theorems_find___redArg(v___x_4784_, v_origin_4775_);
                    v___x_4786_ = l_List_isEmpty___redArg(v___x_4785_);
                    if v___x_4786_ == 0 {
                        v___x_4787_ = l_List_appendTR___redArg(v_b_4777_, v___x_4785_);
                        v_a_4779_ = v___x_4787_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4785_);
                        v_a_4779_ = v_b_4777_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4780_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4781_ = lean_nat_add(v_a_4776_, v___x_4780_);
                crate::leanh::lean_dec(v_a_4776_);
                v_a_4776_ = v___x_4781_;
                v_b_4777_ = v_a_4779_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(
    mut v_upperBound_4788_: *mut crate::leanh::LeanObject,
    mut v_s_4789_: *mut crate::leanh::LeanObject,
    mut v_origin_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_b_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(
            v_upperBound_4788_,
            v_s_4789_,
            v_origin_4790_,
            v_a_4791_,
            v_b_4792_,
        );
    crate::leanh::lean_dec_ref(v_origin_4790_);
    crate::leanh::lean_dec_ref(v_s_4789_);
    crate::leanh::lean_dec(v_upperBound_4788_);
    return v_res_4793_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_find___redArg(
    mut v_s_4794_: *mut crate::leanh::LeanObject,
    mut v_origin_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = lean_array_get_size(v_s_4794_);
    v___x_4797_ = crate::leanh::lean_unsigned_to_nat(0);
    v_r_4798_ = crate::leanh::lean_box(0);
    v___x_4799_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(
            v___x_4796_,
            v_s_4794_,
            v_origin_4795_,
            v___x_4797_,
            v_r_4798_,
        );
    return v___x_4799_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(
    mut v_s_4800_: *mut crate::leanh::LeanObject,
    mut v_origin_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_4800_, v_origin_4801_);
    crate::leanh::lean_dec_ref(v_origin_4801_);
    crate::leanh::lean_dec_ref(v_s_4800_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_find(
    mut v_00_u03b1_4803_: *mut crate::leanh::LeanObject,
    mut v_s_4804_: *mut crate::leanh::LeanObject,
    mut v_origin_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_4804_, v_origin_4805_);
    return v___x_4806_;
}
pub unsafe fn l_Lean_Meta_Grind_TheoremsArray_find___boxed(
    mut v_00_u03b1_4807_: *mut crate::leanh::LeanObject,
    mut v_s_4808_: *mut crate::leanh::LeanObject,
    mut v_origin_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4810_ = l_Lean_Meta_Grind_TheoremsArray_find(v_00_u03b1_4807_, v_s_4808_, v_origin_4809_);
    crate::leanh::lean_dec_ref(v_origin_4809_);
    crate::leanh::lean_dec_ref(v_s_4808_);
    return v_res_4810_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(
    mut v_00_u03b1_4811_: *mut crate::leanh::LeanObject,
    mut v_upperBound_4812_: *mut crate::leanh::LeanObject,
    mut v_s_4813_: *mut crate::leanh::LeanObject,
    mut v_origin_4814_: *mut crate::leanh::LeanObject,
    mut v_inst_4815_: *mut crate::leanh::LeanObject,
    mut v_R_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_b_4818_: *mut crate::leanh::LeanObject,
    mut v_c_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4820_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(
            v_upperBound_4812_,
            v_s_4813_,
            v_origin_4814_,
            v_a_4817_,
            v_b_4818_,
        );
    return v___x_4820_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(
    mut v_00_u03b1_4821_: *mut crate::leanh::LeanObject,
    mut v_upperBound_4822_: *mut crate::leanh::LeanObject,
    mut v_s_4823_: *mut crate::leanh::LeanObject,
    mut v_origin_4824_: *mut crate::leanh::LeanObject,
    mut v_inst_4825_: *mut crate::leanh::LeanObject,
    mut v_R_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_b_4828_: *mut crate::leanh::LeanObject,
    mut v_c_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4830_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(
        v_00_u03b1_4821_,
        v_upperBound_4822_,
        v_s_4823_,
        v_origin_4824_,
        v_inst_4825_,
        v_R_4826_,
        v_a_4827_,
        v_b_4828_,
        v_c_4829_,
    );
    crate::leanh::lean_dec_ref(v_origin_4824_);
    crate::leanh::lean_dec_ref(v_s_4823_);
    crate::leanh::lean_dec(v_upperBound_4822_);
    return v_res_4830_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Theorems(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Theorems(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_HeadIndex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
}
