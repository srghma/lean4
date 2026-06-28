// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PP
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Util Init.Grind.Injective Init.Grind.PP Lean.Meta.Tactic.Grind.Arith.CommRing.PP Lean.Meta.Tactic.Grind.Arith.Linear.PP Lean.Meta.Tactic.Grind.AC.PP Lean.Meta.Tactic.Grind.CastLike Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Grind::Injective::{
    initialize_Init_Grind_Injective, runtime_initialize_Init_Grind_Injective,
};
use crate::r#gen::Init::Grind::PP::{initialize_Init_Grind_PP, runtime_initialize_Init_Grind_PP};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_toArray___redArg, l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_Node_isEmpty___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_Expr_isConst,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isFalse, l_Lean_Expr_isTrue, l_Lean_Expr_sort___override,
    l_Lean_mkApp3, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_joinSep, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_ppExpr,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProof};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_isLitValue;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::lean_is_matcher;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::PP::{
    initialize_Lean_Meta_Tactic_Grind_AC_PP, l_Lean_Meta_Grind_AC_pp_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::PP::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP,
    l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage, l_Lean_Meta_Grind_Arith_CommRing_pp_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model, l_Lean_Meta_Grind_Arith_Cutsat_mkModel,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::PP::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP, l_Lean_Meta_Grind_Arith_Linear_pp_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::l_Lean_Meta_Grind_Arith_quoteIfArithTerm;
use crate::r#gen::Lean::Meta::Tactic::Grind::CastLike::{
    initialize_Lean_Meta_Tactic_Grind_CastLike, l_Lean_Meta_Grind_isCastLikeApp,
    l_Lean_Meta_Grind_isCastLikeDeclName, runtime_initialize_Lean_Meta_Tactic_Grind_CastLike,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::l_Lean_Meta_Grind_ppPattern;
use crate::r#gen::Lean::Meta::Tactic::Grind::Theorems::l_Lean_Meta_Grind_Origin_pp;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg,
    l_Lean_Meta_Grind_Goal_getENode, l_Lean_Meta_Grind_Goal_getENode_x3f,
    l_Lean_Meta_Grind_Goal_getEqcs, l_Lean_Meta_Grind_Goal_getTarget_x3f,
    l_Lean_Meta_Grind_SplitSource_toMessageData, l_Lean_Meta_Grind_grind_debug,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [110, 111, 100, 101, 95, 100, 101, 102, 0],
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8764611631698118843 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 157, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 91, 99, 116, 111, 114, 93, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [44, 32, 91, 118, 97, 108, 93, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Goal_ppState___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 111, 97, 108, 58, 0],
    };
static mut l_Lean_Meta_Grind_Goal_ppState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppState___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Goal_ppState___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Goal_ppState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ppGoals___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Meta_Grind_ppGoals___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ppGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_ppGoals___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ppGoals___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value:
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
static mut l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value:
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
        110, 101, 115, 116, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value) as *mut crate::leanh::LeanObject,11081308864005098561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value:
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
    m_data: [108, 101, 102, 116, 73, 110, 118, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value) as *mut crate::leanh::LeanObject,4547445378961686909 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value:
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
    m_data: [99, 97, 115, 116, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        4894447893040251571 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value:
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
    m_data: [105, 116, 101, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value:
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
            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18356704233129443855 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value:
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
    m_data: [100, 105, 116, 101, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value:
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
            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        8391571994004792969 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedResult_default: u8 = 0;
pub static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult: u8 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_ppEqc___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [101, 113, 99, 0],
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_ppEqc___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13700905132686059645 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_ppEqc___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ppEqc___closed__3_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_ppEqc___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ppEqc___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_ppEqc___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_ppEqc___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ppEqc___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [70, 97, 108, 115, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 112, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,1514733921013856056 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [84, 114, 117, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        69, 113, 117, 105, 118, 97, 108, 101, 110, 99, 101, 32, 99, 108, 97, 115, 115, 101, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2_value:
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
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value:
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
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value:
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
    m_data: [111, 116, 104, 101, 114, 115, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8_value:
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
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value) as *mut crate::leanh::LeanObject,11262269099723811472 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 109, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value) as *mut crate::leanh::LeanObject,17884542580662885801 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [69, 45, 109, 97, 116, 99, 104, 105, 110, 103, 32, 112, 97, 116, 116, 101, 114, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 105, 103, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,4634307013023994764 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 117, 116, 115, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15469340725812647537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value: crate::leanh::LeanStringObject<
    41,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        65, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 115, 97, 116, 105, 115, 102, 121, 105,
        110, 103, 32, 108, 105, 110, 101, 97, 114, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110,
        116, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 109, 105, 116, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7708385730198571152 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [84, 104, 114, 101, 115, 104, 111, 108, 100, 115, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 105, 109, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value) as *mut crate::leanh::LeanObject,6724977332459863754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value: crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 116, 101, 114, 109, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 44, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 58, 32, 96, 40, 103, 101, 110, 32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [41, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value: crate::leanh::LeanStringObject<72> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 99, 97, 115, 101, 45, 115, 112, 108, 105, 116, 115, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 44, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 58, 32, 96, 40, 115, 112, 108, 105, 116, 115, 32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 69, 45, 109, 97, 116, 99, 104, 105, 110, 103, 32, 114, 111, 117, 110, 100, 115, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 44, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 58, 32, 96, 40, 101, 109, 97, 116, 99, 104, 32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value: crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 98, 121, 32, 69, 45, 109, 97, 116, 99, 104, 105, 110, 103, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 44, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 58, 32, 96, 40, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13724376360221892060 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [93, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 111, 117, 114, 99, 101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 97, 115, 101, 32, 97, 110, 97, 108, 121, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 99, 116, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value) as *mut crate::leanh::LeanObject,5835464875110000645 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [65, 115, 115, 101, 114, 116, 101, 100, 32, 102, 97, 99, 116, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_goalDiagToMessageData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_goalDiagToMessageData___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_goalDiagToMessageData___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0_value:
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
        71, 111, 97, 108, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3223_ = l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5;
    v___x_3224_ = l_Lean_MessageData_ofFormat(v___x_3223_);
    return v___x_3224_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_ppENodeRef(
    mut v_goal_3225_: *mut crate::leanh::LeanObject,
    mut v_e_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
    mut v_a_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v_idx_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v_a_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3232_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_goal_3225_, v_e_3226_);
                if crate::leanh::lean_obj_tag(v___x_3232_) == 1 {
                    v_val_3233_ = crate::leanh::lean_ctor_get(v___x_3232_, 0);
                    crate::leanh::lean_inc(v_val_3233_);
                    crate::leanh::lean_dec_ref_known(v___x_3232_, 1);
                    crate::leanh::lean_inc(v_a_3230_);
                    crate::leanh::lean_inc_ref(v_a_3229_);
                    crate::leanh::lean_inc(v_a_3228_);
                    crate::leanh::lean_inc_ref(v_a_3227_);
                    crate::leanh::lean_inc_ref(v_e_3226_);
                    v___x_3234_ =
                        lean_infer_type(v_e_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
                    if crate::leanh::lean_obj_tag(v___x_3234_) == 0 {
                        v_a_3235_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                        crate::leanh::lean_inc_n(v_a_3235_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3234_, 1);
                        v___x_3236_ = l_Lean_Meta_getLevel(
                            v_a_3235_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3236_) == 0 {
                            v_a_3237_ = crate::leanh::lean_ctor_get(v___x_3236_, 0);
                            v_isSharedCheck_3252_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3236_)) as u8;
                            if v_isSharedCheck_3252_ == 0 {
                                v___x_3239_ = v___x_3236_;
                                v_isShared_3240_ = v_isSharedCheck_3252_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3237_);
                                crate::leanh::lean_dec(v___x_3236_);
                                v___x_3239_ = crate::leanh::lean_box(0);
                                v_isShared_3240_ = v_isSharedCheck_3252_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3235_);
                            crate::leanh::lean_dec(v_val_3233_);
                            crate::leanh::lean_dec_ref(v_e_3226_);
                            v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3236_, 0);
                            v_isSharedCheck_3260_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3236_)) as u8;
                            if v_isSharedCheck_3260_ == 0 {
                                v___x_3255_ = v___x_3236_;
                                v_isShared_3256_ = v_isSharedCheck_3260_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3253_);
                                crate::leanh::lean_dec(v___x_3236_);
                                v___x_3255_ = crate::leanh::lean_box(0);
                                v_isShared_3256_ = v_isSharedCheck_3260_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3233_);
                        crate::leanh::lean_dec_ref(v_e_3226_);
                        v_a_3261_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                        v_isSharedCheck_3268_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3234_)) as u8;
                        if v_isSharedCheck_3268_ == 0 {
                            v___x_3263_ = v___x_3234_;
                            v_isShared_3264_ = v_isSharedCheck_3268_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3261_);
                            crate::leanh::lean_dec(v___x_3234_);
                            v___x_3263_ = crate::leanh::lean_box(0);
                            v_isShared_3264_ = v_isSharedCheck_3268_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3232_);
                    crate::leanh::lean_dec_ref(v_e_3226_);
                    v___x_3269_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6_once),
                        _init_l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6,
                    );
                    v___x_3270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3269_);
                    return v___x_3270_;
                }
            }
            1 => {
                v_idx_3241_ = crate::leanh::lean_ctor_get(v_val_3233_, 7);
                crate::leanh::lean_inc(v_idx_3241_);
                crate::leanh::lean_dec(v_val_3233_);
                v___x_3242_ = l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3;
                v___x_3243_ = crate::leanh::lean_box(0);
                v___x_3244_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3244_, 0, v_a_3237_);
                crate::leanh::lean_ctor_set(v___x_3244_, 1, v___x_3243_);
                v___x_3245_ = l_Lean_mkConst(v___x_3242_, v___x_3244_);
                v___x_3246_ = l_Lean_mkNatLit(v_idx_3241_);
                v___x_3247_ = l_Lean_mkApp3(v___x_3245_, v___x_3246_, v_a_3235_, v_e_3226_);
                v___x_3248_ = l_Lean_MessageData_ofExpr(v___x_3247_);
                if v_isShared_3240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3250_;
            }
            3 => {
                if v_isShared_3256_ == 0 {
                    v___x_3258_ = v___x_3255_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3258_;
            }
            5 => {
                if v_isShared_3264_ == 0 {
                    v___x_3266_ = v___x_3263_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
                    v___x_3266_ = v_reuseFailAlloc_3267_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_ppENodeRef___boxed(
    mut v_goal_3271_: *mut crate::leanh::LeanObject,
    mut v_e_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3278_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
        v_goal_3271_,
        v_e_3272_,
        v_a_3273_,
        v_a_3274_,
        v_a_3275_,
        v_a_3276_,
    );
    crate::leanh::lean_dec(v_a_3276_);
    crate::leanh::lean_dec_ref(v_a_3275_);
    crate::leanh::lean_dec(v_a_3274_);
    crate::leanh::lean_dec_ref(v_a_3273_);
    crate::leanh::lean_dec_ref(v_goal_3271_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_Meta_Grind_ppENodeRef___redArg(
    mut v_e_3279_: *mut crate::leanh::LeanObject,
    mut v_a_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3286_ = lean_st_ref_get(v_a_3280_);
    v___x_3287_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
        v___x_3286_,
        v_e_3279_,
        v_a_3281_,
        v_a_3282_,
        v_a_3283_,
        v_a_3284_,
    );
    crate::leanh::lean_dec(v___x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_Lean_Meta_Grind_ppENodeRef___redArg___boxed(
    mut v_e_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Lean_Meta_Grind_ppENodeRef___redArg(
        v_e_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_,
    );
    crate::leanh::lean_dec(v_a_3293_);
    crate::leanh::lean_dec_ref(v_a_3292_);
    crate::leanh::lean_dec(v_a_3291_);
    crate::leanh::lean_dec_ref(v_a_3290_);
    crate::leanh::lean_dec(v_a_3289_);
    return v_res_3295_;
}
pub unsafe fn l_Lean_Meta_Grind_ppENodeRef(
    mut v_e_3296_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Lean_Meta_Grind_ppENodeRef___redArg(
        v_e_3296_, v_a_3297_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_,
    );
    return v___x_3308_;
}
pub unsafe fn l_Lean_Meta_Grind_ppENodeRef___boxed(
    mut v_e_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l_Lean_Meta_Grind_ppENodeRef(
        v_e_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_,
        v_a_3317_, v_a_3318_, v_a_3319_,
    );
    crate::leanh::lean_dec(v_a_3319_);
    crate::leanh::lean_dec_ref(v_a_3318_);
    crate::leanh::lean_dec(v_a_3317_);
    crate::leanh::lean_dec_ref(v_a_3316_);
    crate::leanh::lean_dec(v_a_3315_);
    crate::leanh::lean_dec_ref(v_a_3314_);
    crate::leanh::lean_dec(v_a_3313_);
    crate::leanh::lean_dec_ref(v_a_3312_);
    crate::leanh::lean_dec(v_a_3311_);
    crate::leanh::lean_dec(v_a_3310_);
    return v_res_3321_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1;
    v___x_3326_ = l_Lean_MessageData_ofFormat(v___x_3325_);
    return v___x_3326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(
    mut v_goal_3327_: *mut crate::leanh::LeanObject,
    mut v_as_3328_: *mut crate::leanh::LeanObject,
    mut v_sz_3329_: usize,
    mut v_i_3330_: usize,
    mut v_b_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3337_ = lean_usize_dec_lt(v_i_3330_, v_sz_3329_);
                if v___x_3337_ == 0 {
                    v___x_3338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3338_, 0, v_b_3331_);
                    return v___x_3338_;
                } else {
                    v_a_3339_ = lean_array_uget_borrowed(v_as_3328_, v_i_3330_);
                    crate::leanh::lean_inc(v_a_3339_);
                    v___x_3340_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                        v_goal_3327_,
                        v_a_3339_,
                        v___y_3332_,
                        v___y_3333_,
                        v___y_3334_,
                        v___y_3335_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3340_) == 0 {
                        v_a_3341_ = crate::leanh::lean_ctor_get(v___x_3340_, 0);
                        crate::leanh::lean_inc(v_a_3341_);
                        crate::leanh::lean_dec_ref_known(v___x_3340_, 1);
                        v___x_3342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2);
                        v___x_3343_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3343_, 0, v_b_3331_);
                        crate::leanh::lean_ctor_set(v___x_3343_, 1, v___x_3342_);
                        v___x_3344_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3343_);
                        crate::leanh::lean_ctor_set(v___x_3344_, 1, v_a_3341_);
                        v___x_3345_ = 1usize;
                        v___x_3346_ = lean_usize_add(v_i_3330_, v___x_3345_);
                        v_i_3330_ = v___x_3346_;
                        v_b_3331_ = v___x_3344_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3331_);
                        return v___x_3340_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___boxed(
    mut v_goal_3348_: *mut crate::leanh::LeanObject,
    mut v_as_3349_: *mut crate::leanh::LeanObject,
    mut v_sz_3350_: *mut crate::leanh::LeanObject,
    mut v_i_3351_: *mut crate::leanh::LeanObject,
    mut v_b_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3358_: usize = 0;
    let mut v_i_boxed_3359_: usize = 0;
    let mut v_res_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3358_ = crate::leanh::lean_unbox_usize(v_sz_3350_);
    crate::leanh::lean_dec(v_sz_3350_);
    v_i_boxed_3359_ = crate::leanh::lean_unbox_usize(v_i_3351_);
    crate::leanh::lean_dec(v_i_3351_);
    v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(v_goal_3348_, v_as_3349_, v_sz_boxed_3358_, v_i_boxed_3359_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
    crate::leanh::lean_dec(v___y_3356_);
    crate::leanh::lean_dec_ref(v___y_3355_);
    crate::leanh::lean_dec(v___y_3354_);
    crate::leanh::lean_dec_ref(v___y_3353_);
    crate::leanh::lean_dec_ref(v_as_3349_);
    crate::leanh::lean_dec_ref(v_goal_3348_);
    return v_res_3360_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(
    mut v_goal_3361_: *mut crate::leanh::LeanObject,
    mut v_x_3362_: *mut crate::leanh::LeanObject,
    mut v_x_3363_: *mut crate::leanh::LeanObject,
    mut v_x_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3376_: usize = 0;
    let mut v___x_3377_: usize = 0;
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3362_) == 5 {
                    v_fn_3379_ = crate::leanh::lean_ctor_get(v_x_3362_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3379_);
                    v_arg_3380_ = crate::leanh::lean_ctor_get(v_x_3362_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3380_);
                    crate::leanh::lean_dec_ref_known(v_x_3362_, 2);
                    v___x_3381_ = lean_array_set(v_x_3363_, v_x_3364_, v_arg_3380_);
                    v___x_3382_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3383_ = lean_nat_sub(v_x_3364_, v___x_3382_);
                    crate::leanh::lean_dec(v_x_3364_);
                    v_x_3362_ = v_fn_3379_;
                    v_x_3363_ = v___x_3381_;
                    v_x_3364_ = v___x_3383_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_3364_);
                    v___x_3385_ = l_Lean_Expr_isConst(v_x_3362_);
                    if v___x_3385_ == 0 {
                        v___x_3386_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                            v_goal_3361_,
                            v_x_3362_,
                            v___y_3365_,
                            v___y_3366_,
                            v___y_3367_,
                            v___y_3368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3386_) == 0 {
                            v_a_3387_ = crate::leanh::lean_ctor_get(v___x_3386_, 0);
                            crate::leanh::lean_inc(v_a_3387_);
                            crate::leanh::lean_dec_ref_known(v___x_3386_, 1);
                            v_r_3371_ = v_a_3387_;
                            v___y_3372_ = v___y_3365_;
                            v___y_3373_ = v___y_3366_;
                            v___y_3374_ = v___y_3367_;
                            v___y_3375_ = v___y_3368_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_x_3363_);
                            return v___x_3386_;
                        }
                    } else {
                        v___x_3388_ = l_Lean_MessageData_ofExpr(v_x_3362_);
                        v_r_3371_ = v___x_3388_;
                        v___y_3372_ = v___y_3365_;
                        v___y_3373_ = v___y_3366_;
                        v___y_3374_ = v___y_3367_;
                        v___y_3375_ = v___y_3368_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_3376_ = lean_array_size(v_x_3363_);
                v___x_3377_ = 0usize;
                v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(v_goal_3361_, v_x_3363_, v_sz_3376_, v___x_3377_, v_r_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
                crate::leanh::lean_dec_ref(v_x_3363_);
                return v___x_3378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1___boxed(
    mut v_goal_3389_: *mut crate::leanh::LeanObject,
    mut v_x_3390_: *mut crate::leanh::LeanObject,
    mut v_x_3391_: *mut crate::leanh::LeanObject,
    mut v_x_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3398_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(v_goal_3389_, v_x_3390_, v_x_3391_, v_x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
    crate::leanh::lean_dec(v___y_3396_);
    crate::leanh::lean_dec_ref(v___y_3395_);
    crate::leanh::lean_dec(v___y_3394_);
    crate::leanh::lean_dec_ref(v___y_3393_);
    crate::leanh::lean_dec_ref(v_goal_3389_);
    return v_res_3398_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = crate::leanh::lean_box(0);
    v_dummy_3400_ = l_Lean_Expr_sort___override(v___x_3399_);
    return v_dummy_3400_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(
    mut v_goal_3401_: *mut crate::leanh::LeanObject,
    mut v_e_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
    mut v_a_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v___y_3430_: u8 = 0;
    let mut v_dummy_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: u8 = 0;
    let mut v_a_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3402_);
                v___x_3408_ =
                    l_Lean_Meta_isLitValue(v_e_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
                if crate::leanh::lean_obj_tag(v___x_3408_) == 0 {
                    v_a_3409_ = crate::leanh::lean_ctor_get(v___x_3408_, 0);
                    crate::leanh::lean_inc(v_a_3409_);
                    crate::leanh::lean_dec_ref_known(v___x_3408_, 1);
                    v___x_3437_ = l_Lean_Expr_isApp(v_e_3402_);
                    if v___x_3437_ == 0 {
                        crate::leanh::lean_dec(v_a_3409_);
                        v___y_3430_ = v___x_3437_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3438_ = (crate::leanh::lean_unbox(v_a_3409_) as u8);
                        crate::leanh::lean_dec(v_a_3409_);
                        if v___x_3438_ == 0 {
                            v___y_3430_ = v___x_3437_;
                            state = 6;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3402_);
                    v_a_3439_ = crate::leanh::lean_ctor_get(v___x_3408_, 0);
                    v_isSharedCheck_3446_ = (!crate::leanh::lean_is_exclusive(v___x_3408_)) as u8;
                    if v_isSharedCheck_3446_ == 0 {
                        v___x_3441_ = v___x_3408_;
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3439_);
                        crate::leanh::lean_dec(v___x_3408_);
                        v___x_3441_ = crate::leanh::lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3411_ =
                    l_Lean_Meta_ppExpr(v_e_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
                if crate::leanh::lean_obj_tag(v___x_3411_) == 0 {
                    v_a_3412_ = crate::leanh::lean_ctor_get(v___x_3411_, 0);
                    v_isSharedCheck_3420_ = (!crate::leanh::lean_is_exclusive(v___x_3411_)) as u8;
                    if v_isSharedCheck_3420_ == 0 {
                        v___x_3414_ = v___x_3411_;
                        v_isShared_3415_ = v_isSharedCheck_3420_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3412_);
                        crate::leanh::lean_dec(v___x_3411_);
                        v___x_3414_ = crate::leanh::lean_box(0);
                        v_isShared_3415_ = v_isSharedCheck_3420_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3421_ = crate::leanh::lean_ctor_get(v___x_3411_, 0);
                    v_isSharedCheck_3428_ = (!crate::leanh::lean_is_exclusive(v___x_3411_)) as u8;
                    if v_isSharedCheck_3428_ == 0 {
                        v___x_3423_ = v___x_3411_;
                        v_isShared_3424_ = v_isSharedCheck_3428_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3421_);
                        crate::leanh::lean_dec(v___x_3411_);
                        v___x_3423_ = crate::leanh::lean_box(0);
                        v_isShared_3424_ = v_isSharedCheck_3428_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3416_ = l_Lean_MessageData_ofFormat(v_a_3412_);
                if v_isShared_3415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3414_, 0, v___x_3416_);
                    v___x_3418_ = v___x_3414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
                    v___x_3418_ = v_reuseFailAlloc_3419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3418_;
            }
            4 => {
                if v_isShared_3424_ == 0 {
                    v___x_3426_ = v___x_3423_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
                    v___x_3426_ = v_reuseFailAlloc_3427_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3426_;
            }
            6 => {
                if v___y_3430_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_dummy_3431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0);
                    v_nargs_3432_ = l_Lean_Expr_getAppNumArgs(v_e_3402_);
                    crate::leanh::lean_inc(v_nargs_3432_);
                    v___x_3433_ = lean_mk_array(v_nargs_3432_, v_dummy_3431_);
                    v___x_3434_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3435_ = lean_nat_sub(v_nargs_3432_, v___x_3434_);
                    crate::leanh::lean_dec(v_nargs_3432_);
                    v___x_3436_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(v_goal_3401_, v_e_3402_, v___x_3433_, v___x_3435_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
                    return v___x_3436_;
                }
            }
            7 => {
                if v_isShared_3442_ == 0 {
                    v___x_3444_ = v___x_3441_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___boxed(
    mut v_goal_3447_: *mut crate::leanh::LeanObject,
    mut v_e_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(
        v_goal_3447_,
        v_e_3448_,
        v_a_3449_,
        v_a_3450_,
        v_a_3451_,
        v_a_3452_,
    );
    crate::leanh::lean_dec(v_a_3452_);
    crate::leanh::lean_dec_ref(v_a_3451_);
    crate::leanh::lean_dec(v_a_3450_);
    crate::leanh::lean_dec_ref(v_a_3449_);
    crate::leanh::lean_dec_ref(v_goal_3447_);
    return v_res_3454_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(
    mut v_opts_3455_: *mut crate::leanh::LeanObject,
    mut v_opt_3456_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3457_ = crate::leanh::lean_ctor_get(v_opt_3456_, 0);
    v_defValue_3458_ = crate::leanh::lean_ctor_get(v_opt_3456_, 1);
    v_map_3459_ = crate::leanh::lean_ctor_get(v_opts_3455_, 0);
    v___x_3460_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3459_,
            v_name_3457_,
        );
    if crate::leanh::lean_obj_tag(v___x_3460_) == 0 {
        let mut v___x_3461_: u8 = 0;
        v___x_3461_ = (crate::leanh::lean_unbox(v_defValue_3458_) as u8);
        return v___x_3461_;
    } else {
        let mut v_val_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3462_ = crate::leanh::lean_ctor_get(v___x_3460_, 0);
        crate::leanh::lean_inc(v_val_3462_);
        crate::leanh::lean_dec_ref_known(v___x_3460_, 1);
        if crate::leanh::lean_obj_tag(v_val_3462_) == 1 {
            let mut v_v_3463_: u8 = 0;
            v_v_3463_ = crate::leanh::lean_ctor_get_uint8(v_val_3462_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3462_, 0);
            return v_v_3463_;
        } else {
            let mut v___x_3464_: u8 = 0;
            crate::leanh::lean_dec(v_val_3462_);
            v___x_3464_ = (crate::leanh::lean_unbox(v_defValue_3458_) as u8);
            return v___x_3464_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0___boxed(
    mut v_opts_3465_: *mut crate::leanh::LeanObject,
    mut v_opt_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3467_: u8 = 0;
    let mut v_r_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v_opts_3465_, v_opt_3466_);
    crate::leanh::lean_dec_ref(v_opt_3466_);
    crate::leanh::lean_dec_ref(v_opts_3465_);
    v_r_3468_ = crate::leanh::lean_box((v_res_3467_) as usize);
    return v_r_3468_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3470_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0;
    v___x_3471_ = l_Lean_stringToMessageData(v___x_3470_);
    return v___x_3471_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3;
    v___x_3476_ = l_Lean_MessageData_ofFormat(v___x_3475_);
    return v___x_3476_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6;
    v___x_3481_ = l_Lean_MessageData_ofFormat(v___x_3480_);
    return v___x_3481_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8;
    v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
    return v___x_3484_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10;
    v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
    mut v_goal_3488_: *mut crate::leanh::LeanObject,
    mut v_e_3489_: *mut crate::leanh::LeanObject,
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interpreted_3527_: u8 = 0;
    let mut v_ctor_3528_: u8 = 0;
    let mut v_r_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: u8 = 0;
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3557_: u8 = 0;
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3489_);
                v___x_3520_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                    v_goal_3488_,
                    v_e_3489_,
                    v_a_3490_,
                    v_a_3491_,
                    v_a_3492_,
                    v_a_3493_,
                );
                if crate::leanh::lean_obj_tag(v___x_3520_) == 0 {
                    v_a_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                    crate::leanh::lean_inc(v_a_3521_);
                    crate::leanh::lean_dec_ref_known(v___x_3520_, 1);
                    crate::leanh::lean_inc_ref(v_e_3489_);
                    v___x_3522_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_3488_, v_e_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
                    if crate::leanh::lean_obj_tag(v___x_3522_) == 0 {
                        v_a_3523_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                        crate::leanh::lean_inc(v_a_3523_);
                        crate::leanh::lean_dec_ref_known(v___x_3522_, 1);
                        crate::leanh::lean_inc_ref(v_e_3489_);
                        v___x_3524_ = l_Lean_Meta_Grind_Goal_getENode(
                            v_goal_3488_,
                            v_e_3489_,
                            v_a_3490_,
                            v_a_3491_,
                            v_a_3492_,
                            v_a_3493_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                            v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                            crate::leanh::lean_inc(v_a_3525_);
                            crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                            v_root_3526_ = crate::leanh::lean_ctor_get(v_a_3525_, 2);
                            crate::leanh::lean_inc_ref(v_root_3526_);
                            v_interpreted_3527_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_3525_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 1)
                                    as u32,
                            );
                            v_ctor_3528_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_3525_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 2)
                                    as u32,
                            );
                            crate::leanh::lean_dec(v_a_3525_);
                            v___x_3545_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
                            v___x_3546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3546_, 0, v_a_3521_);
                            crate::leanh::lean_ctor_set(v___x_3546_, 1, v___x_3545_);
                            v___x_3547_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3547_, 0, v___x_3546_);
                            crate::leanh::lean_ctor_set(v___x_3547_, 1, v_a_3523_);
                            v___x_3548_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_3489_, v_root_3526_);
                            if v___x_3548_ == 0 {
                                v___x_3549_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                                    v_goal_3488_,
                                    v_root_3526_,
                                    v_a_3490_,
                                    v_a_3491_,
                                    v_a_3492_,
                                    v_a_3493_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3549_) == 0 {
                                    v_a_3550_ = crate::leanh::lean_ctor_get(v___x_3549_, 0);
                                    crate::leanh::lean_inc(v_a_3550_);
                                    crate::leanh::lean_dec_ref_known(v___x_3549_, 1);
                                    v___x_3551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11);
                                    v___x_3552_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3551_);
                                    crate::leanh::lean_ctor_set(v___x_3552_, 1, v_a_3550_);
                                    v___x_3553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3553_, 0, v___x_3547_);
                                    crate::leanh::lean_ctor_set(v___x_3553_, 1, v___x_3552_);
                                    v_r_3538_ = v___x_3553_;
                                    v___y_3539_ = v_a_3490_;
                                    v___y_3540_ = v_a_3491_;
                                    v___y_3541_ = v_a_3492_;
                                    v___y_3542_ = v_a_3493_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_3547_, 2);
                                    crate::leanh::lean_dec_ref(v_e_3489_);
                                    return v___x_3549_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_root_3526_);
                                v_r_3538_ = v___x_3547_;
                                v___y_3539_ = v_a_3490_;
                                v___y_3540_ = v_a_3491_;
                                v___y_3541_ = v_a_3492_;
                                v___y_3542_ = v_a_3493_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3523_);
                            crate::leanh::lean_dec(v_a_3521_);
                            crate::leanh::lean_dec_ref(v_e_3489_);
                            v_a_3554_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                            v_isSharedCheck_3561_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                            if v_isSharedCheck_3561_ == 0 {
                                v___x_3556_ = v___x_3524_;
                                v_isShared_3557_ = v_isSharedCheck_3561_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3554_);
                                crate::leanh::lean_dec(v___x_3524_);
                                v___x_3556_ = crate::leanh::lean_box(0);
                                v_isShared_3557_ = v_isSharedCheck_3561_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3521_);
                        crate::leanh::lean_dec_ref(v_e_3489_);
                        return v___x_3522_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3489_);
                    return v___x_3520_;
                }
            }
            1 => {
                v_options_3501_ = crate::leanh::lean_ctor_get(v___y_3499_, 2);
                v___x_3502_ = l_Lean_Meta_Grind_grind_debug;
                v___x_3503_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v_options_3501_, v___x_3502_);
                if v___x_3503_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3489_);
                    v___x_3504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3504_, 0, v_r_3496_);
                    return v___x_3504_;
                } else {
                    v___x_3505_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v_goal_3488_, v_e_3489_);
                    crate::leanh::lean_dec_ref(v_e_3489_);
                    if crate::leanh::lean_obj_tag(v___x_3505_) == 1 {
                        v_val_3506_ = crate::leanh::lean_ctor_get(v___x_3505_, 0);
                        crate::leanh::lean_inc(v_val_3506_);
                        crate::leanh::lean_dec_ref_known(v___x_3505_, 1);
                        v___x_3507_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                            v_goal_3488_,
                            v_val_3506_,
                            v___y_3497_,
                            v___y_3498_,
                            v___y_3499_,
                            v___y_3500_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3507_) == 0 {
                            v_a_3508_ = crate::leanh::lean_ctor_get(v___x_3507_, 0);
                            v_isSharedCheck_3518_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3507_)) as u8;
                            if v_isSharedCheck_3518_ == 0 {
                                v___x_3510_ = v___x_3507_;
                                v_isShared_3511_ = v_isSharedCheck_3518_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3508_);
                                crate::leanh::lean_dec(v___x_3507_);
                                v___x_3510_ = crate::leanh::lean_box(0);
                                v_isShared_3511_ = v_isSharedCheck_3518_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_r_3496_);
                            return v___x_3507_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3505_);
                        v___x_3519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3519_, 0, v_r_3496_);
                        return v___x_3519_;
                    }
                }
            }
            2 => {
                v___x_3512_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1);
                v___x_3513_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                crate::leanh::lean_ctor_set(v___x_3513_, 1, v_a_3508_);
                v___x_3514_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3514_, 0, v_r_3496_);
                crate::leanh::lean_ctor_set(v___x_3514_, 1, v___x_3513_);
                if v_isShared_3511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3514_);
                    v___x_3516_ = v___x_3510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
                    v___x_3516_ = v_reuseFailAlloc_3517_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3516_;
            }
            4 => {
                if v_ctor_3528_ == 0 {
                    v_r_3496_ = v_r_3530_;
                    v___y_3497_ = v___y_3531_;
                    v___y_3498_ = v___y_3532_;
                    v___y_3499_ = v___y_3533_;
                    v___y_3500_ = v___y_3534_;
                    state = 1;
                    continue;
                } else {
                    v___x_3535_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4);
                    v___x_3536_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v_r_3530_);
                    crate::leanh::lean_ctor_set(v___x_3536_, 1, v___x_3535_);
                    v_r_3496_ = v___x_3536_;
                    v___y_3497_ = v___y_3531_;
                    v___y_3498_ = v___y_3532_;
                    v___y_3499_ = v___y_3533_;
                    v___y_3500_ = v___y_3534_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_interpreted_3527_ == 0 {
                    v_r_3530_ = v_r_3538_;
                    v___y_3531_ = v___y_3539_;
                    v___y_3532_ = v___y_3540_;
                    v___y_3533_ = v___y_3541_;
                    v___y_3534_ = v___y_3542_;
                    state = 4;
                    continue;
                } else {
                    v___x_3543_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7);
                    v___x_3544_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v_r_3538_);
                    crate::leanh::lean_ctor_set(v___x_3544_, 1, v___x_3543_);
                    v_r_3530_ = v___x_3544_;
                    v___y_3531_ = v___y_3539_;
                    v___y_3532_ = v___y_3540_;
                    v___y_3533_ = v___y_3541_;
                    v___y_3534_ = v___y_3542_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_3557_ == 0 {
                    v___x_3559_ = v___x_3556_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
                    v___x_3559_ = v_reuseFailAlloc_3560_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___boxed(
    mut v_goal_3562_: *mut crate::leanh::LeanObject,
    mut v_e_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_a_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3569_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
        v_goal_3562_,
        v_e_3563_,
        v_a_3564_,
        v_a_3565_,
        v_a_3566_,
        v_a_3567_,
    );
    crate::leanh::lean_dec(v_a_3567_);
    crate::leanh::lean_dec_ref(v_a_3566_);
    crate::leanh::lean_dec(v_a_3565_);
    crate::leanh::lean_dec_ref(v_a_3564_);
    crate::leanh::lean_dec_ref(v_goal_3562_);
    return v_res_3569_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(
    mut v_goal_3570_: *mut crate::leanh::LeanObject,
    mut v_x_3571_: *mut crate::leanh::LeanObject,
    mut v_x_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
    mut v___y_3574_: *mut crate::leanh::LeanObject,
    mut v___y_3575_: *mut crate::leanh::LeanObject,
    mut v___y_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3571_) == 0 {
                    v___x_3578_ = l_List_reverse___redArg(v_x_3572_);
                    v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                    return v___x_3579_;
                } else {
                    v_head_3580_ = crate::leanh::lean_ctor_get(v_x_3571_, 0);
                    v_tail_3581_ = crate::leanh::lean_ctor_get(v_x_3571_, 1);
                    v_isSharedCheck_3599_ = (!crate::leanh::lean_is_exclusive(v_x_3571_)) as u8;
                    if v_isSharedCheck_3599_ == 0 {
                        v___x_3583_ = v_x_3571_;
                        v_isShared_3584_ = v_isSharedCheck_3599_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3581_);
                        crate::leanh::lean_inc(v_head_3580_);
                        crate::leanh::lean_dec(v_x_3571_);
                        v___x_3583_ = crate::leanh::lean_box(0);
                        v_isShared_3584_ = v_isSharedCheck_3599_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3585_ = l_Lean_Meta_Grind_Goal_ppENodeRef(
                    v_goal_3570_,
                    v_head_3580_,
                    v___y_3573_,
                    v___y_3574_,
                    v___y_3575_,
                    v___y_3576_,
                );
                if crate::leanh::lean_obj_tag(v___x_3585_) == 0 {
                    v_a_3586_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                    crate::leanh::lean_inc(v_a_3586_);
                    crate::leanh::lean_dec_ref_known(v___x_3585_, 1);
                    if v_isShared_3584_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3583_, 1, v_x_3572_);
                        crate::leanh::lean_ctor_set(v___x_3583_, 0, v_a_3586_);
                        v___x_3588_ = v___x_3583_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3590_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3586_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_x_3572_);
                        v___x_3588_ = v_reuseFailAlloc_3590_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3583_);
                    crate::leanh::lean_dec(v_tail_3581_);
                    crate::leanh::lean_dec(v_x_3572_);
                    v_a_3591_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                    v_isSharedCheck_3598_ = (!crate::leanh::lean_is_exclusive(v___x_3585_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v___x_3593_ = v___x_3585_;
                        v_isShared_3594_ = v_isSharedCheck_3598_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3591_);
                        crate::leanh::lean_dec(v___x_3585_);
                        v___x_3593_ = crate::leanh::lean_box(0);
                        v_isShared_3594_ = v_isSharedCheck_3598_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3571_ = v_tail_3581_;
                v_x_3572_ = v___x_3588_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3594_ == 0 {
                    v___x_3596_ = v___x_3593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
                    v___x_3596_ = v_reuseFailAlloc_3597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0___boxed(
    mut v_goal_3600_: *mut crate::leanh::LeanObject,
    mut v_x_3601_: *mut crate::leanh::LeanObject,
    mut v_x_3602_: *mut crate::leanh::LeanObject,
    mut v___y_3603_: *mut crate::leanh::LeanObject,
    mut v___y_3604_: *mut crate::leanh::LeanObject,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(
        v_goal_3600_,
        v_x_3601_,
        v_x_3602_,
        v___y_3603_,
        v___y_3604_,
        v___y_3605_,
        v___y_3606_,
    );
    crate::leanh::lean_dec(v___y_3606_);
    crate::leanh::lean_dec_ref(v___y_3605_);
    crate::leanh::lean_dec(v___y_3604_);
    crate::leanh::lean_dec_ref(v___y_3603_);
    crate::leanh::lean_dec_ref(v_goal_3600_);
    return v_res_3608_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1;
    v___x_3613_ = l_Lean_MessageData_ofFormat(v___x_3612_);
    return v___x_3613_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3617_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4;
    v___x_3618_ = l_Lean_MessageData_ofFormat(v___x_3617_);
    return v___x_3618_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7;
    v___x_3623_ = l_Lean_MessageData_ofFormat(v___x_3622_);
    return v___x_3623_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10;
    v___x_3628_ = l_Lean_MessageData_ofFormat(v___x_3627_);
    return v___x_3628_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(
    mut v_goal_3629_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3630_: *mut crate::leanh::LeanObject,
    mut v_b_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3630_) == 0 {
                    v___x_3637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3637_, 0, v_b_3631_);
                    return v___x_3637_;
                } else {
                    v_head_3638_ = crate::leanh::lean_ctor_get(v_as_x27_3630_, 0);
                    v_tail_3639_ = crate::leanh::lean_ctor_get(v_as_x27_3630_, 1);
                    v___x_3640_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3641_ = l_List_lengthTR___redArg(v_head_3638_);
                    v___x_3642_ = lean_nat_dec_lt(v___x_3640_, v___x_3641_);
                    crate::leanh::lean_dec(v___x_3641_);
                    if v___x_3642_ == 0 {
                        v_as_x27_3630_ = v_tail_3639_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3644_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_head_3638_);
                        v___x_3645_ =
                            l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(
                                v_goal_3629_,
                                v_head_3638_,
                                v___x_3644_,
                                v___y_3632_,
                                v___y_3633_,
                                v___y_3634_,
                                v___y_3635_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3645_) == 0 {
                            v_a_3646_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                            crate::leanh::lean_inc(v_a_3646_);
                            crate::leanh::lean_dec_ref_known(v___x_3645_, 1);
                            v___x_3647_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
                            v___x_3648_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3648_, 0, v_b_3631_);
                            crate::leanh::lean_ctor_set(v___x_3648_, 1, v___x_3647_);
                            v___x_3649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
                            v___x_3650_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3648_);
                            crate::leanh::lean_ctor_set(v___x_3650_, 1, v___x_3649_);
                            v___x_3651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8);
                            v___x_3652_ = l_Lean_MessageData_joinSep(v_a_3646_, v___x_3651_);
                            v___x_3653_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3653_, 0, v___x_3650_);
                            crate::leanh::lean_ctor_set(v___x_3653_, 1, v___x_3652_);
                            v___x_3654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
                            v___x_3655_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                            crate::leanh::lean_ctor_set(v___x_3655_, 1, v___x_3654_);
                            v_as_x27_3630_ = v_tail_3639_;
                            v_b_3631_ = v___x_3655_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3631_);
                            v_a_3657_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                            v_isSharedCheck_3664_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3645_)) as u8;
                            if v_isSharedCheck_3664_ == 0 {
                                v___x_3659_ = v___x_3645_;
                                v_isShared_3660_ = v_isSharedCheck_3664_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3657_);
                                crate::leanh::lean_dec(v___x_3645_);
                                v___x_3659_ = crate::leanh::lean_box(0);
                                v_isShared_3660_ = v_isSharedCheck_3664_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3660_ == 0 {
                    v___x_3662_ = v___x_3659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___boxed(
    mut v_goal_3665_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3666_: *mut crate::leanh::LeanObject,
    mut v_b_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(
        v_goal_3665_,
        v_as_x27_3666_,
        v_b_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
        v___y_3671_,
    );
    crate::leanh::lean_dec(v___y_3671_);
    crate::leanh::lean_dec_ref(v___y_3670_);
    crate::leanh::lean_dec(v___y_3669_);
    crate::leanh::lean_dec_ref(v___y_3668_);
    crate::leanh::lean_dec(v_as_x27_3666_);
    crate::leanh::lean_dec_ref(v_goal_3665_);
    return v_res_3673_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(
    mut v_goal_3674_: *mut crate::leanh::LeanObject,
    mut v_as_3675_: *mut crate::leanh::LeanObject,
    mut v_sz_3676_: usize,
    mut v_i_3677_: usize,
    mut v_b_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v_a_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: usize = 0;
    let mut v___x_3703_: usize = 0;
    let mut v_reuseFailAlloc_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3713_: u8 = 0;
    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3717_: u8 = 0;
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut v_unused_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3684_ = lean_usize_dec_lt(v_i_3677_, v_sz_3676_);
                if v___x_3684_ == 0 {
                    v___x_3685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v_b_3678_);
                    return v___x_3685_;
                } else {
                    v_snd_3686_ = crate::leanh::lean_ctor_get(v_b_3678_, 1);
                    v_isSharedCheck_3722_ = (!crate::leanh::lean_is_exclusive(v_b_3678_)) as u8;
                    if v_isSharedCheck_3722_ == 0 {
                        v_unused_3723_ = crate::leanh::lean_ctor_get(v_b_3678_, 0);
                        crate::leanh::lean_dec(v_unused_3723_);
                        v___x_3688_ = v_b_3678_;
                        v_isShared_3689_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3686_);
                        crate::leanh::lean_dec(v_b_3678_);
                        v___x_3688_ = crate::leanh::lean_box(0);
                        v_isShared_3689_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3690_ = lean_array_uget_borrowed(v_as_3675_, v_i_3677_);
                crate::leanh::lean_inc(v_a_3690_);
                v___x_3691_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3674_,
                    v_a_3690_,
                    v___y_3679_,
                    v___y_3680_,
                    v___y_3681_,
                    v___y_3682_,
                );
                if crate::leanh::lean_obj_tag(v___x_3691_) == 0 {
                    v_a_3692_ = crate::leanh::lean_ctor_get(v___x_3691_, 0);
                    crate::leanh::lean_inc(v_a_3692_);
                    crate::leanh::lean_dec_ref_known(v___x_3691_, 1);
                    v_self_3693_ = crate::leanh::lean_ctor_get(v_a_3692_, 0);
                    crate::leanh::lean_inc_ref(v_self_3693_);
                    crate::leanh::lean_dec(v_a_3692_);
                    v___x_3694_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
                            v_goal_3674_,
                            v_self_3693_,
                            v___y_3679_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                        crate::leanh::lean_inc(v_a_3695_);
                        crate::leanh::lean_dec_ref_known(v___x_3694_, 1);
                        v___x_3696_ = crate::leanh::lean_box(0);
                        v___x_3697_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
                        v___x_3698_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3698_, 0, v_snd_3686_);
                        crate::leanh::lean_ctor_set(v___x_3698_, 1, v___x_3697_);
                        v___x_3699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3699_, 0, v___x_3698_);
                        crate::leanh::lean_ctor_set(v___x_3699_, 1, v_a_3695_);
                        if v_isShared_3689_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3688_, 1, v___x_3699_);
                            crate::leanh::lean_ctor_set(v___x_3688_, 0, v___x_3696_);
                            v___x_3701_ = v___x_3688_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3705_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3696_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3699_);
                            v___x_3701_ = v_reuseFailAlloc_3705_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3688_);
                        crate::leanh::lean_dec(v_snd_3686_);
                        v_a_3706_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                        v_isSharedCheck_3713_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3694_)) as u8;
                        if v_isSharedCheck_3713_ == 0 {
                            v___x_3708_ = v___x_3694_;
                            v_isShared_3709_ = v_isSharedCheck_3713_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3706_);
                            crate::leanh::lean_dec(v___x_3694_);
                            v___x_3708_ = crate::leanh::lean_box(0);
                            v_isShared_3709_ = v_isSharedCheck_3713_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3688_);
                    crate::leanh::lean_dec(v_snd_3686_);
                    v_a_3714_ = crate::leanh::lean_ctor_get(v___x_3691_, 0);
                    v_isSharedCheck_3721_ = (!crate::leanh::lean_is_exclusive(v___x_3691_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v___x_3716_ = v___x_3691_;
                        v_isShared_3717_ = v_isSharedCheck_3721_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3714_);
                        crate::leanh::lean_dec(v___x_3691_);
                        v___x_3716_ = crate::leanh::lean_box(0);
                        v_isShared_3717_ = v_isSharedCheck_3721_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3702_ = 1usize;
                v___x_3703_ = lean_usize_add(v_i_3677_, v___x_3702_);
                v_i_3677_ = v___x_3703_;
                v_b_3678_ = v___x_3701_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3709_ == 0 {
                    v___x_3711_ = v___x_3708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
                    v___x_3711_ = v_reuseFailAlloc_3712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3711_;
            }
            5 => {
                if v_isShared_3717_ == 0 {
                    v___x_3719_ = v___x_3716_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
                    v___x_3719_ = v_reuseFailAlloc_3720_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_goal_3724_: *mut crate::leanh::LeanObject,
    mut v_as_3725_: *mut crate::leanh::LeanObject,
    mut v_sz_3726_: *mut crate::leanh::LeanObject,
    mut v_i_3727_: *mut crate::leanh::LeanObject,
    mut v_b_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3734_: usize = 0;
    let mut v_i_boxed_3735_: usize = 0;
    let mut v_res_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3734_ = crate::leanh::lean_unbox_usize(v_sz_3726_);
    crate::leanh::lean_dec(v_sz_3726_);
    v_i_boxed_3735_ = crate::leanh::lean_unbox_usize(v_i_3727_);
    crate::leanh::lean_dec(v_i_3727_);
    v_res_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_3724_, v_as_3725_, v_sz_boxed_3734_, v_i_boxed_3735_, v_b_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
    crate::leanh::lean_dec(v___y_3732_);
    crate::leanh::lean_dec_ref(v___y_3731_);
    crate::leanh::lean_dec(v___y_3730_);
    crate::leanh::lean_dec_ref(v___y_3729_);
    crate::leanh::lean_dec_ref(v_as_3725_);
    crate::leanh::lean_dec_ref(v_goal_3724_);
    return v_res_3736_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(
    mut v_goal_3737_: *mut crate::leanh::LeanObject,
    mut v_as_3738_: *mut crate::leanh::LeanObject,
    mut v_sz_3739_: usize,
    mut v_i_3740_: usize,
    mut v_b_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v_a_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: usize = 0;
    let mut v___x_3766_: usize = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_a_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3747_ = lean_usize_dec_lt(v_i_3740_, v_sz_3739_);
                if v___x_3747_ == 0 {
                    v___x_3748_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3748_, 0, v_b_3741_);
                    return v___x_3748_;
                } else {
                    v_snd_3749_ = crate::leanh::lean_ctor_get(v_b_3741_, 1);
                    v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v_b_3741_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v_unused_3786_ = crate::leanh::lean_ctor_get(v_b_3741_, 0);
                        crate::leanh::lean_dec(v_unused_3786_);
                        v___x_3751_ = v_b_3741_;
                        v_isShared_3752_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3749_);
                        crate::leanh::lean_dec(v_b_3741_);
                        v___x_3751_ = crate::leanh::lean_box(0);
                        v_isShared_3752_ = v_isSharedCheck_3785_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3753_ = lean_array_uget_borrowed(v_as_3738_, v_i_3740_);
                crate::leanh::lean_inc(v_a_3753_);
                v___x_3754_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3737_,
                    v_a_3753_,
                    v___y_3742_,
                    v___y_3743_,
                    v___y_3744_,
                    v___y_3745_,
                );
                if crate::leanh::lean_obj_tag(v___x_3754_) == 0 {
                    v_a_3755_ = crate::leanh::lean_ctor_get(v___x_3754_, 0);
                    crate::leanh::lean_inc(v_a_3755_);
                    crate::leanh::lean_dec_ref_known(v___x_3754_, 1);
                    v_self_3756_ = crate::leanh::lean_ctor_get(v_a_3755_, 0);
                    crate::leanh::lean_inc_ref(v_self_3756_);
                    crate::leanh::lean_dec(v_a_3755_);
                    v___x_3757_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
                            v_goal_3737_,
                            v_self_3756_,
                            v___y_3742_,
                            v___y_3743_,
                            v___y_3744_,
                            v___y_3745_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3757_) == 0 {
                        v_a_3758_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                        crate::leanh::lean_inc(v_a_3758_);
                        crate::leanh::lean_dec_ref_known(v___x_3757_, 1);
                        v___x_3759_ = crate::leanh::lean_box(0);
                        v___x_3760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
                        v___x_3761_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3761_, 0, v_snd_3749_);
                        crate::leanh::lean_ctor_set(v___x_3761_, 1, v___x_3760_);
                        v___x_3762_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3761_);
                        crate::leanh::lean_ctor_set(v___x_3762_, 1, v_a_3758_);
                        if v_isShared_3752_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3751_, 1, v___x_3762_);
                            crate::leanh::lean_ctor_set(v___x_3751_, 0, v___x_3759_);
                            v___x_3764_ = v___x_3751_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3768_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3759_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 1, v___x_3762_);
                            v___x_3764_ = v_reuseFailAlloc_3768_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3751_);
                        crate::leanh::lean_dec(v_snd_3749_);
                        v_a_3769_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                        v_isSharedCheck_3776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3757_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3771_ = v___x_3757_;
                            v_isShared_3772_ = v_isSharedCheck_3776_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3769_);
                            crate::leanh::lean_dec(v___x_3757_);
                            v___x_3771_ = crate::leanh::lean_box(0);
                            v_isShared_3772_ = v_isSharedCheck_3776_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3751_);
                    crate::leanh::lean_dec(v_snd_3749_);
                    v_a_3777_ = crate::leanh::lean_ctor_get(v___x_3754_, 0);
                    v_isSharedCheck_3784_ = (!crate::leanh::lean_is_exclusive(v___x_3754_)) as u8;
                    if v_isSharedCheck_3784_ == 0 {
                        v___x_3779_ = v___x_3754_;
                        v_isShared_3780_ = v_isSharedCheck_3784_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3777_);
                        crate::leanh::lean_dec(v___x_3754_);
                        v___x_3779_ = crate::leanh::lean_box(0);
                        v_isShared_3780_ = v_isSharedCheck_3784_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3765_ = 1usize;
                v___x_3766_ = lean_usize_add(v_i_3740_, v___x_3765_);
                v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_3737_, v_as_3738_, v_sz_3739_, v___x_3766_, v___x_3764_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
                return v___x_3767_;
            }
            3 => {
                if v_isShared_3772_ == 0 {
                    v___x_3774_ = v___x_3771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
                    v___x_3774_ = v_reuseFailAlloc_3775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3774_;
            }
            5 => {
                if v_isShared_3780_ == 0 {
                    v___x_3782_ = v___x_3779_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
                    v___x_3782_ = v_reuseFailAlloc_3783_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3___boxed(
    mut v_goal_3787_: *mut crate::leanh::LeanObject,
    mut v_as_3788_: *mut crate::leanh::LeanObject,
    mut v_sz_3789_: *mut crate::leanh::LeanObject,
    mut v_i_3790_: *mut crate::leanh::LeanObject,
    mut v_b_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3797_: usize = 0;
    let mut v_i_boxed_3798_: usize = 0;
    let mut v_res_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3797_ = crate::leanh::lean_unbox_usize(v_sz_3789_);
    crate::leanh::lean_dec(v_sz_3789_);
    v_i_boxed_3798_ = crate::leanh::lean_unbox_usize(v_i_3790_);
    crate::leanh::lean_dec(v_i_3790_);
    v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_3787_, v_as_3788_, v_sz_boxed_3797_, v_i_boxed_3798_, v_b_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
    crate::leanh::lean_dec(v___y_3795_);
    crate::leanh::lean_dec_ref(v___y_3794_);
    crate::leanh::lean_dec(v___y_3793_);
    crate::leanh::lean_dec_ref(v___y_3792_);
    crate::leanh::lean_dec_ref(v_as_3788_);
    crate::leanh::lean_dec_ref(v_goal_3787_);
    return v_res_3799_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(
    mut v_init_3800_: *mut crate::leanh::LeanObject,
    mut v_goal_3801_: *mut crate::leanh::LeanObject,
    mut v_n_3802_: *mut crate::leanh::LeanObject,
    mut v_b_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3812_: usize = 0;
    let mut v___x_3813_: usize = 0;
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v_fst_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_a_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_vs_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3841_: usize = 0;
    let mut v___x_3842_: usize = 0;
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v_fst_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v_a_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3802_) == 0 {
                    v_cs_3809_ = crate::leanh::lean_ctor_get(v_n_3802_, 0);
                    v___x_3810_ = crate::leanh::lean_box(0);
                    v___x_3811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3811_, 0, v___x_3810_);
                    crate::leanh::lean_ctor_set(v___x_3811_, 1, v_b_3803_);
                    v_sz_3812_ = lean_array_size(v_cs_3809_);
                    v___x_3813_ = 0usize;
                    v___x_3814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_3800_, v_goal_3801_, v_cs_3809_, v_sz_3812_, v___x_3813_, v___x_3811_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
                    if crate::leanh::lean_obj_tag(v___x_3814_) == 0 {
                        v_a_3815_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
                        v_isSharedCheck_3829_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3814_)) as u8;
                        if v_isSharedCheck_3829_ == 0 {
                            v___x_3817_ = v___x_3814_;
                            v_isShared_3818_ = v_isSharedCheck_3829_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3815_);
                            crate::leanh::lean_dec(v___x_3814_);
                            v___x_3817_ = crate::leanh::lean_box(0);
                            v_isShared_3818_ = v_isSharedCheck_3829_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3830_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
                        v_isSharedCheck_3837_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3814_)) as u8;
                        if v_isSharedCheck_3837_ == 0 {
                            v___x_3832_ = v___x_3814_;
                            v_isShared_3833_ = v_isSharedCheck_3837_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3830_);
                            crate::leanh::lean_dec(v___x_3814_);
                            v___x_3832_ = crate::leanh::lean_box(0);
                            v_isShared_3833_ = v_isSharedCheck_3837_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3838_ = crate::leanh::lean_ctor_get(v_n_3802_, 0);
                    v___x_3839_ = crate::leanh::lean_box(0);
                    v___x_3840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3839_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v_b_3803_);
                    v_sz_3841_ = lean_array_size(v_vs_3838_);
                    v___x_3842_ = 0usize;
                    v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_3801_, v_vs_3838_, v_sz_3841_, v___x_3842_, v___x_3840_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
                    if crate::leanh::lean_obj_tag(v___x_3843_) == 0 {
                        v_a_3844_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3858_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3858_ == 0 {
                            v___x_3846_ = v___x_3843_;
                            v_isShared_3847_ = v_isSharedCheck_3858_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3844_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_3846_ = crate::leanh::lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_3858_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3859_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3866_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3866_ == 0 {
                            v___x_3861_ = v___x_3843_;
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3859_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_3861_ = crate::leanh::lean_box(0);
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3819_ = crate::leanh::lean_ctor_get(v_a_3815_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3819_) == 0 {
                    v_snd_3820_ = crate::leanh::lean_ctor_get(v_a_3815_, 1);
                    crate::leanh::lean_inc(v_snd_3820_);
                    crate::leanh::lean_dec(v_a_3815_);
                    v___x_3821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3821_, 0, v_snd_3820_);
                    if v_isShared_3818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3821_);
                        v___x_3823_ = v___x_3817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3824_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
                        v___x_3823_ = v_reuseFailAlloc_3824_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3819_);
                    crate::leanh::lean_dec(v_a_3815_);
                    v_val_3825_ = crate::leanh::lean_ctor_get(v_fst_3819_, 0);
                    crate::leanh::lean_inc(v_val_3825_);
                    crate::leanh::lean_dec_ref_known(v_fst_3819_, 1);
                    if v_isShared_3818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3817_, 0, v_val_3825_);
                        v___x_3827_ = v___x_3817_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_val_3825_);
                        v___x_3827_ = v_reuseFailAlloc_3828_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3823_;
            }
            3 => {
                return v___x_3827_;
            }
            4 => {
                if v_isShared_3833_ == 0 {
                    v___x_3835_ = v___x_3832_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
                    v___x_3835_ = v_reuseFailAlloc_3836_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3835_;
            }
            6 => {
                v_fst_3848_ = crate::leanh::lean_ctor_get(v_a_3844_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3848_) == 0 {
                    v_snd_3849_ = crate::leanh::lean_ctor_get(v_a_3844_, 1);
                    crate::leanh::lean_inc(v_snd_3849_);
                    crate::leanh::lean_dec(v_a_3844_);
                    v___x_3850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3850_, 0, v_snd_3849_);
                    if v_isShared_3847_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3850_);
                        v___x_3852_ = v___x_3846_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
                        v___x_3852_ = v_reuseFailAlloc_3853_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3848_);
                    crate::leanh::lean_dec(v_a_3844_);
                    v_val_3854_ = crate::leanh::lean_ctor_get(v_fst_3848_, 0);
                    crate::leanh::lean_inc(v_val_3854_);
                    crate::leanh::lean_dec_ref_known(v_fst_3848_, 1);
                    if v_isShared_3847_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3846_, 0, v_val_3854_);
                        v___x_3856_ = v___x_3846_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3857_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_val_3854_);
                        v___x_3856_ = v_reuseFailAlloc_3857_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3852_;
            }
            8 => {
                return v___x_3856_;
            }
            9 => {
                if v_isShared_3862_ == 0 {
                    v___x_3864_ = v___x_3861_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
                    v___x_3864_ = v_reuseFailAlloc_3865_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(
    mut v_init_3867_: *mut crate::leanh::LeanObject,
    mut v_goal_3868_: *mut crate::leanh::LeanObject,
    mut v_as_3869_: *mut crate::leanh::LeanObject,
    mut v_sz_3870_: usize,
    mut v_i_3871_: usize,
    mut v_b_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v_a_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_unused_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3878_ = lean_usize_dec_lt(v_i_3871_, v_sz_3870_);
                if v___x_3878_ == 0 {
                    v___x_3879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3879_, 0, v_b_3872_);
                    return v___x_3879_;
                } else {
                    v_snd_3880_ = crate::leanh::lean_ctor_get(v_b_3872_, 1);
                    v_isSharedCheck_3914_ = (!crate::leanh::lean_is_exclusive(v_b_3872_)) as u8;
                    if v_isSharedCheck_3914_ == 0 {
                        v_unused_3915_ = crate::leanh::lean_ctor_get(v_b_3872_, 0);
                        crate::leanh::lean_dec(v_unused_3915_);
                        v___x_3882_ = v_b_3872_;
                        v_isShared_3883_ = v_isSharedCheck_3914_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3880_);
                        crate::leanh::lean_dec(v_b_3872_);
                        v___x_3882_ = crate::leanh::lean_box(0);
                        v_isShared_3883_ = v_isSharedCheck_3914_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3884_ = lean_array_uget_borrowed(v_as_3869_, v_i_3871_);
                crate::leanh::lean_inc(v_snd_3880_);
                v___x_3885_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_3867_, v_goal_3868_, v_a_3884_, v_snd_3880_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
                if crate::leanh::lean_obj_tag(v___x_3885_) == 0 {
                    v_a_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                    v_isSharedCheck_3905_ = (!crate::leanh::lean_is_exclusive(v___x_3885_)) as u8;
                    if v_isSharedCheck_3905_ == 0 {
                        v___x_3888_ = v___x_3885_;
                        v_isShared_3889_ = v_isSharedCheck_3905_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3886_);
                        crate::leanh::lean_dec(v___x_3885_);
                        v___x_3888_ = crate::leanh::lean_box(0);
                        v_isShared_3889_ = v_isSharedCheck_3905_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3882_);
                    crate::leanh::lean_dec(v_snd_3880_);
                    v_a_3906_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                    v_isSharedCheck_3913_ = (!crate::leanh::lean_is_exclusive(v___x_3885_)) as u8;
                    if v_isSharedCheck_3913_ == 0 {
                        v___x_3908_ = v___x_3885_;
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3906_);
                        crate::leanh::lean_dec(v___x_3885_);
                        v___x_3908_ = crate::leanh::lean_box(0);
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3886_) == 0 {
                    v___x_3890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3890_, 0, v_a_3886_);
                    if v_isShared_3883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3890_);
                        v___x_3892_ = v___x_3882_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3890_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_snd_3880_);
                        v___x_3892_ = v_reuseFailAlloc_3896_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3888_);
                    crate::leanh::lean_dec(v_snd_3880_);
                    v_a_3897_ = crate::leanh::lean_ctor_get(v_a_3886_, 0);
                    crate::leanh::lean_inc(v_a_3897_);
                    crate::leanh::lean_dec_ref_known(v_a_3886_, 1);
                    v___x_3898_ = crate::leanh::lean_box(0);
                    if v_isShared_3883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3882_, 1, v_a_3897_);
                        crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3898_);
                        v___x_3900_ = v___x_3882_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_a_3897_);
                        v___x_3900_ = v_reuseFailAlloc_3904_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3888_, 0, v___x_3892_);
                    v___x_3894_ = v___x_3888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3894_;
            }
            5 => {
                v___x_3901_ = 1usize;
                v___x_3902_ = lean_usize_add(v_i_3871_, v___x_3901_);
                v_i_3871_ = v___x_3902_;
                v_b_3872_ = v___x_3900_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3909_ == 0 {
                    v___x_3911_ = v___x_3908_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2___boxed(
    mut v_init_3916_: *mut crate::leanh::LeanObject,
    mut v_goal_3917_: *mut crate::leanh::LeanObject,
    mut v_as_3918_: *mut crate::leanh::LeanObject,
    mut v_sz_3919_: *mut crate::leanh::LeanObject,
    mut v_i_3920_: *mut crate::leanh::LeanObject,
    mut v_b_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3927_: usize = 0;
    let mut v_i_boxed_3928_: usize = 0;
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3927_ = crate::leanh::lean_unbox_usize(v_sz_3919_);
    crate::leanh::lean_dec(v_sz_3919_);
    v_i_boxed_3928_ = crate::leanh::lean_unbox_usize(v_i_3920_);
    crate::leanh::lean_dec(v_i_3920_);
    v_res_3929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_3916_, v_goal_3917_, v_as_3918_, v_sz_boxed_3927_, v_i_boxed_3928_, v_b_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
    crate::leanh::lean_dec(v___y_3925_);
    crate::leanh::lean_dec_ref(v___y_3924_);
    crate::leanh::lean_dec(v___y_3923_);
    crate::leanh::lean_dec_ref(v___y_3922_);
    crate::leanh::lean_dec_ref(v_as_3918_);
    crate::leanh::lean_dec_ref(v_goal_3917_);
    crate::leanh::lean_dec_ref(v_init_3916_);
    return v_res_3929_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1___boxed(
    mut v_init_3930_: *mut crate::leanh::LeanObject,
    mut v_goal_3931_: *mut crate::leanh::LeanObject,
    mut v_n_3932_: *mut crate::leanh::LeanObject,
    mut v_b_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3939_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_3930_, v_goal_3931_, v_n_3932_, v_b_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
    crate::leanh::lean_dec(v___y_3937_);
    crate::leanh::lean_dec_ref(v___y_3936_);
    crate::leanh::lean_dec(v___y_3935_);
    crate::leanh::lean_dec_ref(v___y_3934_);
    crate::leanh::lean_dec_ref(v_n_3932_);
    crate::leanh::lean_dec_ref(v_goal_3931_);
    crate::leanh::lean_dec_ref(v_init_3930_);
    return v_res_3939_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(
    mut v_goal_3940_: *mut crate::leanh::LeanObject,
    mut v_as_3941_: *mut crate::leanh::LeanObject,
    mut v_sz_3942_: usize,
    mut v_i_3943_: usize,
    mut v_b_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v_a_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: usize = 0;
    let mut v___x_3969_: usize = 0;
    let mut v_reuseFailAlloc_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3975_: u8 = 0;
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3979_: u8 = 0;
    let mut v_a_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_unused_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3950_ = lean_usize_dec_lt(v_i_3943_, v_sz_3942_);
                if v___x_3950_ == 0 {
                    v___x_3951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3951_, 0, v_b_3944_);
                    return v___x_3951_;
                } else {
                    v_snd_3952_ = crate::leanh::lean_ctor_get(v_b_3944_, 1);
                    v_isSharedCheck_3988_ = (!crate::leanh::lean_is_exclusive(v_b_3944_)) as u8;
                    if v_isSharedCheck_3988_ == 0 {
                        v_unused_3989_ = crate::leanh::lean_ctor_get(v_b_3944_, 0);
                        crate::leanh::lean_dec(v_unused_3989_);
                        v___x_3954_ = v_b_3944_;
                        v_isShared_3955_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3952_);
                        crate::leanh::lean_dec(v_b_3944_);
                        v___x_3954_ = crate::leanh::lean_box(0);
                        v_isShared_3955_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3956_ = lean_array_uget_borrowed(v_as_3941_, v_i_3943_);
                crate::leanh::lean_inc(v_a_3956_);
                v___x_3957_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3940_,
                    v_a_3956_,
                    v___y_3945_,
                    v___y_3946_,
                    v___y_3947_,
                    v___y_3948_,
                );
                if crate::leanh::lean_obj_tag(v___x_3957_) == 0 {
                    v_a_3958_ = crate::leanh::lean_ctor_get(v___x_3957_, 0);
                    crate::leanh::lean_inc(v_a_3958_);
                    crate::leanh::lean_dec_ref_known(v___x_3957_, 1);
                    v_self_3959_ = crate::leanh::lean_ctor_get(v_a_3958_, 0);
                    crate::leanh::lean_inc_ref(v_self_3959_);
                    crate::leanh::lean_dec(v_a_3958_);
                    v___x_3960_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
                            v_goal_3940_,
                            v_self_3959_,
                            v___y_3945_,
                            v___y_3946_,
                            v___y_3947_,
                            v___y_3948_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3960_) == 0 {
                        v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                        crate::leanh::lean_inc(v_a_3961_);
                        crate::leanh::lean_dec_ref_known(v___x_3960_, 1);
                        v___x_3962_ = crate::leanh::lean_box(0);
                        v___x_3963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
                        v___x_3964_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3964_, 0, v_snd_3952_);
                        crate::leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                        v___x_3965_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3964_);
                        crate::leanh::lean_ctor_set(v___x_3965_, 1, v_a_3961_);
                        if v_isShared_3955_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3954_, 1, v___x_3965_);
                            crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3962_);
                            v___x_3967_ = v___x_3954_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3971_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3962_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 1, v___x_3965_);
                            v___x_3967_ = v_reuseFailAlloc_3971_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3954_);
                        crate::leanh::lean_dec(v_snd_3952_);
                        v_a_3972_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                        v_isSharedCheck_3979_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3960_)) as u8;
                        if v_isSharedCheck_3979_ == 0 {
                            v___x_3974_ = v___x_3960_;
                            v_isShared_3975_ = v_isSharedCheck_3979_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3972_);
                            crate::leanh::lean_dec(v___x_3960_);
                            v___x_3974_ = crate::leanh::lean_box(0);
                            v_isShared_3975_ = v_isSharedCheck_3979_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3954_);
                    crate::leanh::lean_dec(v_snd_3952_);
                    v_a_3980_ = crate::leanh::lean_ctor_get(v___x_3957_, 0);
                    v_isSharedCheck_3987_ = (!crate::leanh::lean_is_exclusive(v___x_3957_)) as u8;
                    if v_isSharedCheck_3987_ == 0 {
                        v___x_3982_ = v___x_3957_;
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3980_);
                        crate::leanh::lean_dec(v___x_3957_);
                        v___x_3982_ = crate::leanh::lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3987_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3968_ = 1usize;
                v___x_3969_ = lean_usize_add(v_i_3943_, v___x_3968_);
                v_i_3943_ = v___x_3969_;
                v_b_3944_ = v___x_3967_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3975_ == 0 {
                    v___x_3977_ = v___x_3974_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
                    v___x_3977_ = v_reuseFailAlloc_3978_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3977_;
            }
            5 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3986_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5___boxed(
    mut v_goal_3990_: *mut crate::leanh::LeanObject,
    mut v_as_3991_: *mut crate::leanh::LeanObject,
    mut v_sz_3992_: *mut crate::leanh::LeanObject,
    mut v_i_3993_: *mut crate::leanh::LeanObject,
    mut v_b_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4000_: usize = 0;
    let mut v_i_boxed_4001_: usize = 0;
    let mut v_res_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4000_ = crate::leanh::lean_unbox_usize(v_sz_3992_);
    crate::leanh::lean_dec(v_sz_3992_);
    v_i_boxed_4001_ = crate::leanh::lean_unbox_usize(v_i_3993_);
    crate::leanh::lean_dec(v_i_3993_);
    v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_3990_, v_as_3991_, v_sz_boxed_4000_, v_i_boxed_4001_, v_b_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
    crate::leanh::lean_dec(v___y_3998_);
    crate::leanh::lean_dec_ref(v___y_3997_);
    crate::leanh::lean_dec(v___y_3996_);
    crate::leanh::lean_dec_ref(v___y_3995_);
    crate::leanh::lean_dec_ref(v_as_3991_);
    crate::leanh::lean_dec_ref(v_goal_3990_);
    return v_res_4002_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(
    mut v_goal_4003_: *mut crate::leanh::LeanObject,
    mut v_as_4004_: *mut crate::leanh::LeanObject,
    mut v_sz_4005_: usize,
    mut v_i_4006_: usize,
    mut v_b_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v_a_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_unused_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4013_ = lean_usize_dec_lt(v_i_4006_, v_sz_4005_);
                if v___x_4013_ == 0 {
                    v___x_4014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4014_, 0, v_b_4007_);
                    return v___x_4014_;
                } else {
                    v_snd_4015_ = crate::leanh::lean_ctor_get(v_b_4007_, 1);
                    v_isSharedCheck_4051_ = (!crate::leanh::lean_is_exclusive(v_b_4007_)) as u8;
                    if v_isSharedCheck_4051_ == 0 {
                        v_unused_4052_ = crate::leanh::lean_ctor_get(v_b_4007_, 0);
                        crate::leanh::lean_dec(v_unused_4052_);
                        v___x_4017_ = v_b_4007_;
                        v_isShared_4018_ = v_isSharedCheck_4051_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4015_);
                        crate::leanh::lean_dec(v_b_4007_);
                        v___x_4017_ = crate::leanh::lean_box(0);
                        v_isShared_4018_ = v_isSharedCheck_4051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4019_ = lean_array_uget_borrowed(v_as_4004_, v_i_4006_);
                crate::leanh::lean_inc(v_a_4019_);
                v___x_4020_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_4003_,
                    v_a_4019_,
                    v___y_4008_,
                    v___y_4009_,
                    v___y_4010_,
                    v___y_4011_,
                );
                if crate::leanh::lean_obj_tag(v___x_4020_) == 0 {
                    v_a_4021_ = crate::leanh::lean_ctor_get(v___x_4020_, 0);
                    crate::leanh::lean_inc(v_a_4021_);
                    crate::leanh::lean_dec_ref_known(v___x_4020_, 1);
                    v_self_4022_ = crate::leanh::lean_ctor_get(v_a_4021_, 0);
                    crate::leanh::lean_inc_ref(v_self_4022_);
                    crate::leanh::lean_dec(v_a_4021_);
                    v___x_4023_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(
                            v_goal_4003_,
                            v_self_4022_,
                            v___y_4008_,
                            v___y_4009_,
                            v___y_4010_,
                            v___y_4011_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4023_) == 0 {
                        v_a_4024_ = crate::leanh::lean_ctor_get(v___x_4023_, 0);
                        crate::leanh::lean_inc(v_a_4024_);
                        crate::leanh::lean_dec_ref_known(v___x_4023_, 1);
                        v___x_4025_ = crate::leanh::lean_box(0);
                        v___x_4026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
                        v___x_4027_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4027_, 0, v_snd_4015_);
                        crate::leanh::lean_ctor_set(v___x_4027_, 1, v___x_4026_);
                        v___x_4028_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4027_);
                        crate::leanh::lean_ctor_set(v___x_4028_, 1, v_a_4024_);
                        if v_isShared_4018_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4017_, 1, v___x_4028_);
                            crate::leanh::lean_ctor_set(v___x_4017_, 0, v___x_4025_);
                            v___x_4030_ = v___x_4017_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4034_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4025_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4028_);
                            v___x_4030_ = v_reuseFailAlloc_4034_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4017_);
                        crate::leanh::lean_dec(v_snd_4015_);
                        v_a_4035_ = crate::leanh::lean_ctor_get(v___x_4023_, 0);
                        v_isSharedCheck_4042_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4023_)) as u8;
                        if v_isSharedCheck_4042_ == 0 {
                            v___x_4037_ = v___x_4023_;
                            v_isShared_4038_ = v_isSharedCheck_4042_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4035_);
                            crate::leanh::lean_dec(v___x_4023_);
                            v___x_4037_ = crate::leanh::lean_box(0);
                            v_isShared_4038_ = v_isSharedCheck_4042_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4017_);
                    crate::leanh::lean_dec(v_snd_4015_);
                    v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4020_, 0);
                    v_isSharedCheck_4050_ = (!crate::leanh::lean_is_exclusive(v___x_4020_)) as u8;
                    if v_isSharedCheck_4050_ == 0 {
                        v___x_4045_ = v___x_4020_;
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4043_);
                        crate::leanh::lean_dec(v___x_4020_);
                        v___x_4045_ = crate::leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4031_ = 1usize;
                v___x_4032_ = lean_usize_add(v_i_4006_, v___x_4031_);
                v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_4003_, v_as_4004_, v_sz_4005_, v___x_4032_, v___x_4030_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
                return v___x_4033_;
            }
            3 => {
                if v_isShared_4038_ == 0 {
                    v___x_4040_ = v___x_4037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4040_;
            }
            5 => {
                if v_isShared_4046_ == 0 {
                    v___x_4048_ = v___x_4045_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2___boxed(
    mut v_goal_4053_: *mut crate::leanh::LeanObject,
    mut v_as_4054_: *mut crate::leanh::LeanObject,
    mut v_sz_4055_: *mut crate::leanh::LeanObject,
    mut v_i_4056_: *mut crate::leanh::LeanObject,
    mut v_b_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4063_: usize = 0;
    let mut v_i_boxed_4064_: usize = 0;
    let mut v_res_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4063_ = crate::leanh::lean_unbox_usize(v_sz_4055_);
    crate::leanh::lean_dec(v_sz_4055_);
    v_i_boxed_4064_ = crate::leanh::lean_unbox_usize(v_i_4056_);
    crate::leanh::lean_dec(v_i_4056_);
    v_res_4065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_4053_, v_as_4054_, v_sz_boxed_4063_, v_i_boxed_4064_, v_b_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
    crate::leanh::lean_dec(v___y_4061_);
    crate::leanh::lean_dec_ref(v___y_4060_);
    crate::leanh::lean_dec(v___y_4059_);
    crate::leanh::lean_dec_ref(v___y_4058_);
    crate::leanh::lean_dec_ref(v_as_4054_);
    crate::leanh::lean_dec_ref(v_goal_4053_);
    return v_res_4065_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(
    mut v_goal_4066_: *mut crate::leanh::LeanObject,
    mut v_t_4067_: *mut crate::leanh::LeanObject,
    mut v_init_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v_a_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4094_: u8 = 0;
    let mut v_fst_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut v_a_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v_a_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4117_: u8 = 0;
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4074_ = crate::leanh::lean_ctor_get(v_t_4067_, 0);
                v_tail_4075_ = crate::leanh::lean_ctor_get(v_t_4067_, 1);
                crate::leanh::lean_inc_ref(v_init_4068_);
                v___x_4076_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_4068_, v_goal_4066_, v_root_4074_, v_init_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
                crate::leanh::lean_dec_ref(v_init_4068_);
                if crate::leanh::lean_obj_tag(v___x_4076_) == 0 {
                    v_a_4077_ = crate::leanh::lean_ctor_get(v___x_4076_, 0);
                    v_isSharedCheck_4113_ = (!crate::leanh::lean_is_exclusive(v___x_4076_)) as u8;
                    if v_isSharedCheck_4113_ == 0 {
                        v___x_4079_ = v___x_4076_;
                        v_isShared_4080_ = v_isSharedCheck_4113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4077_);
                        crate::leanh::lean_dec(v___x_4076_);
                        v___x_4079_ = crate::leanh::lean_box(0);
                        v_isShared_4080_ = v_isSharedCheck_4113_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4114_ = crate::leanh::lean_ctor_get(v___x_4076_, 0);
                    v_isSharedCheck_4121_ = (!crate::leanh::lean_is_exclusive(v___x_4076_)) as u8;
                    if v_isSharedCheck_4121_ == 0 {
                        v___x_4116_ = v___x_4076_;
                        v_isShared_4117_ = v_isSharedCheck_4121_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4114_);
                        crate::leanh::lean_dec(v___x_4076_);
                        v___x_4116_ = crate::leanh::lean_box(0);
                        v_isShared_4117_ = v_isSharedCheck_4121_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4077_) == 0 {
                    v_a_4081_ = crate::leanh::lean_ctor_get(v_a_4077_, 0);
                    crate::leanh::lean_inc(v_a_4081_);
                    crate::leanh::lean_dec_ref_known(v_a_4077_, 1);
                    if v_isShared_4080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4079_, 0, v_a_4081_);
                        v___x_4083_ = v___x_4079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4081_);
                        v___x_4083_ = v_reuseFailAlloc_4084_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4079_);
                    v_a_4085_ = crate::leanh::lean_ctor_get(v_a_4077_, 0);
                    crate::leanh::lean_inc(v_a_4085_);
                    crate::leanh::lean_dec_ref_known(v_a_4077_, 1);
                    v___x_4086_ = crate::leanh::lean_box(0);
                    v___x_4087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                    crate::leanh::lean_ctor_set(v___x_4087_, 1, v_a_4085_);
                    v_sz_4088_ = lean_array_size(v_tail_4075_);
                    v___x_4089_ = 0usize;
                    v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_4066_, v_tail_4075_, v_sz_4088_, v___x_4089_, v___x_4087_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
                    if crate::leanh::lean_obj_tag(v___x_4090_) == 0 {
                        v_a_4091_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
                        v_isSharedCheck_4104_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4090_)) as u8;
                        if v_isSharedCheck_4104_ == 0 {
                            v___x_4093_ = v___x_4090_;
                            v_isShared_4094_ = v_isSharedCheck_4104_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4091_);
                            crate::leanh::lean_dec(v___x_4090_);
                            v___x_4093_ = crate::leanh::lean_box(0);
                            v_isShared_4094_ = v_isSharedCheck_4104_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4105_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
                        v_isSharedCheck_4112_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4090_)) as u8;
                        if v_isSharedCheck_4112_ == 0 {
                            v___x_4107_ = v___x_4090_;
                            v_isShared_4108_ = v_isSharedCheck_4112_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4105_);
                            crate::leanh::lean_dec(v___x_4090_);
                            v___x_4107_ = crate::leanh::lean_box(0);
                            v_isShared_4108_ = v_isSharedCheck_4112_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4083_;
            }
            3 => {
                v_fst_4095_ = crate::leanh::lean_ctor_get(v_a_4091_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4095_) == 0 {
                    v_snd_4096_ = crate::leanh::lean_ctor_get(v_a_4091_, 1);
                    crate::leanh::lean_inc(v_snd_4096_);
                    crate::leanh::lean_dec(v_a_4091_);
                    if v_isShared_4094_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4093_, 0, v_snd_4096_);
                        v___x_4098_ = v___x_4093_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_snd_4096_);
                        v___x_4098_ = v_reuseFailAlloc_4099_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4095_);
                    crate::leanh::lean_dec(v_a_4091_);
                    v_val_4100_ = crate::leanh::lean_ctor_get(v_fst_4095_, 0);
                    crate::leanh::lean_inc(v_val_4100_);
                    crate::leanh::lean_dec_ref_known(v_fst_4095_, 1);
                    if v_isShared_4094_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4093_, 0, v_val_4100_);
                        v___x_4102_ = v___x_4093_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_val_4100_);
                        v___x_4102_ = v_reuseFailAlloc_4103_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4098_;
            }
            5 => {
                return v___x_4102_;
            }
            6 => {
                if v_isShared_4108_ == 0 {
                    v___x_4110_ = v___x_4107_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
                    v___x_4110_ = v_reuseFailAlloc_4111_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4110_;
            }
            8 => {
                if v_isShared_4117_ == 0 {
                    v___x_4119_ = v___x_4116_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
                    v___x_4119_ = v_reuseFailAlloc_4120_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1___boxed(
    mut v_goal_4122_: *mut crate::leanh::LeanObject,
    mut v_t_4123_: *mut crate::leanh::LeanObject,
    mut v_init_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(
        v_goal_4122_,
        v_t_4123_,
        v_init_4124_,
        v___y_4125_,
        v___y_4126_,
        v___y_4127_,
        v___y_4128_,
    );
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    crate::leanh::lean_dec(v___y_4126_);
    crate::leanh::lean_dec_ref(v___y_4125_);
    crate::leanh::lean_dec_ref(v_t_4123_);
    crate::leanh::lean_dec_ref(v_goal_4122_);
    return v_res_4130_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Goal_ppState___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4132_ = l_Lean_Meta_Grind_Goal_ppState___closed__0;
    v_r_4133_ = l_Lean_stringToMessageData(v___x_4132_);
    return v_r_4133_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_ppState(
    mut v_goal_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
    mut v_a_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toGoalState_4140_ = crate::leanh::lean_ctor_get(v_goal_4134_, 0);
    v_exprs_4141_ = crate::leanh::lean_ctor_get(v_toGoalState_4140_, 2);
    v_r_4142_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Goal_ppState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Goal_ppState___closed__1_once),
        _init_l_Lean_Meta_Grind_Goal_ppState___closed__1,
    );
    v___x_4143_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(
        v_goal_4134_,
        v_exprs_4141_,
        v_r_4142_,
        v_a_4135_,
        v_a_4136_,
        v_a_4137_,
        v_a_4138_,
    );
    if crate::leanh::lean_obj_tag(v___x_4143_) == 0 {
        let mut v_a_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4145_: u8 = 0;
        let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4144_ = crate::leanh::lean_ctor_get(v___x_4143_, 0);
        crate::leanh::lean_inc(v_a_4144_);
        crate::leanh::lean_dec_ref_known(v___x_4143_, 1);
        v___x_4145_ = 1;
        v___x_4146_ = l_Lean_Meta_Grind_Goal_getEqcs(v_goal_4134_, v___x_4145_);
        v___x_4147_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(
            v_goal_4134_,
            v___x_4146_,
            v_a_4144_,
            v_a_4135_,
            v_a_4136_,
            v_a_4137_,
            v_a_4138_,
        );
        crate::leanh::lean_dec(v___x_4146_);
        return v___x_4147_;
    } else {
        return v___x_4143_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_ppState___boxed(
    mut v_goal_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ =
        l_Lean_Meta_Grind_Goal_ppState(v_goal_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
    crate::leanh::lean_dec(v_a_4152_);
    crate::leanh::lean_dec_ref(v_a_4151_);
    crate::leanh::lean_dec(v_a_4150_);
    crate::leanh::lean_dec_ref(v_a_4149_);
    crate::leanh::lean_dec_ref(v_goal_4148_);
    return v_res_4154_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(
    mut v_goal_4155_: *mut crate::leanh::LeanObject,
    mut v_as_4156_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4157_: *mut crate::leanh::LeanObject,
    mut v_b_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(
        v_goal_4155_,
        v_as_x27_4157_,
        v_b_4158_,
        v___y_4160_,
        v___y_4161_,
        v___y_4162_,
        v___y_4163_,
    );
    return v___x_4165_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___boxed(
    mut v_goal_4166_: *mut crate::leanh::LeanObject,
    mut v_as_4167_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4168_: *mut crate::leanh::LeanObject,
    mut v_b_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4176_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(
        v_goal_4166_,
        v_as_4167_,
        v_as_x27_4168_,
        v_b_4169_,
        v_a_4170_,
        v___y_4171_,
        v___y_4172_,
        v___y_4173_,
        v___y_4174_,
    );
    crate::leanh::lean_dec(v___y_4174_);
    crate::leanh::lean_dec_ref(v___y_4173_);
    crate::leanh::lean_dec(v___y_4172_);
    crate::leanh::lean_dec_ref(v___y_4171_);
    crate::leanh::lean_dec(v_as_x27_4168_);
    crate::leanh::lean_dec(v_as_4167_);
    crate::leanh::lean_dec_ref(v_goal_4166_);
    return v_res_4176_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = crate::leanh::lean_box(1);
    v___x_4178_ = l_Lean_MessageData_ofFormat(v___x_4177_);
    return v___x_4178_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(
    mut v_as_x27_4179_: *mut crate::leanh::LeanObject,
    mut v_b_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4179_) == 0 {
                    v___x_4186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4186_, 0, v_b_4180_);
                    return v___x_4186_;
                } else {
                    v_head_4187_ = crate::leanh::lean_ctor_get(v_as_x27_4179_, 0);
                    v_tail_4188_ = crate::leanh::lean_ctor_get(v_as_x27_4179_, 1);
                    v___x_4189_ = l_Lean_Meta_Grind_Goal_ppState(
                        v_head_4187_,
                        v___y_4181_,
                        v___y_4182_,
                        v___y_4183_,
                        v___y_4184_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4189_) == 0 {
                        v_a_4190_ = crate::leanh::lean_ctor_get(v___x_4189_, 0);
                        crate::leanh::lean_inc(v_a_4190_);
                        crate::leanh::lean_dec_ref_known(v___x_4189_, 1);
                        v___x_4191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
                        v___x_4192_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4192_, 0, v_b_4180_);
                        crate::leanh::lean_ctor_set(v___x_4192_, 1, v___x_4191_);
                        v___x_4193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
                        crate::leanh::lean_ctor_set(v___x_4193_, 1, v_a_4190_);
                        v_as_x27_4179_ = v_tail_4188_;
                        v_b_4180_ = v___x_4193_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4180_);
                        return v___x_4189_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___boxed(
    mut v_as_x27_4195_: *mut crate::leanh::LeanObject,
    mut v_b_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(
        v_as_x27_4195_,
        v_b_4196_,
        v___y_4197_,
        v___y_4198_,
        v___y_4199_,
        v___y_4200_,
    );
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec(v_as_x27_4195_);
    return v_res_4202_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ppGoals___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4204_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v_r_4205_ = l_Lean_stringToMessageData(v___x_4204_);
    return v_r_4205_;
}
pub unsafe fn l_Lean_Meta_Grind_ppGoals(
    mut v_goals_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4212_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppGoals___closed__1_once),
        _init_l_Lean_Meta_Grind_ppGoals___closed__1,
    );
    v___x_4213_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(
        v_goals_4206_,
        v_r_4212_,
        v_a_4207_,
        v_a_4208_,
        v_a_4209_,
        v_a_4210_,
    );
    return v___x_4213_;
}
pub unsafe fn l_Lean_Meta_Grind_ppGoals___boxed(
    mut v_goals_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4220_ =
        l_Lean_Meta_Grind_ppGoals(v_goals_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
    crate::leanh::lean_dec(v_a_4218_);
    crate::leanh::lean_dec_ref(v_a_4217_);
    crate::leanh::lean_dec(v_a_4216_);
    crate::leanh::lean_dec_ref(v_a_4215_);
    crate::leanh::lean_dec(v_goals_4214_);
    return v_res_4220_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(
    mut v_as_4221_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4222_: *mut crate::leanh::LeanObject,
    mut v_b_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(
        v_as_x27_4222_,
        v_b_4223_,
        v___y_4225_,
        v___y_4226_,
        v___y_4227_,
        v___y_4228_,
    );
    return v___x_4230_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___boxed(
    mut v_as_4231_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4232_: *mut crate::leanh::LeanObject,
    mut v_b_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(
        v_as_4231_,
        v_as_x27_4232_,
        v_b_4233_,
        v_a_4234_,
        v___y_4235_,
        v___y_4236_,
        v___y_4237_,
        v___y_4238_,
    );
    crate::leanh::lean_dec(v___y_4238_);
    crate::leanh::lean_dec_ref(v___y_4237_);
    crate::leanh::lean_dec(v___y_4236_);
    crate::leanh::lean_dec_ref(v___y_4235_);
    crate::leanh::lean_dec(v_as_x27_4232_);
    crate::leanh::lean_dec(v_as_4231_);
    return v_res_4240_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
    mut v_m_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4244_ = crate::leanh::lean_box(0);
    v___x_4245_ = lean_array_push(v_a_4242_, v_m_4241_);
    v___x_4246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4246_, 0, v___x_4244_);
    crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4245_);
    v___x_4247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4246_);
    return v___x_4247_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg___boxed(
    mut v_m_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4251_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
        v_m_4248_, v_a_4249_,
    );
    return v_res_4251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(
    mut v_m_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
        v_m_4252_, v_a_4254_,
    );
    return v___x_4260_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___boxed(
    mut v_m_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(
        v_m_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_,
    );
    crate::leanh::lean_dec(v_a_4267_);
    crate::leanh::lean_dec_ref(v_a_4266_);
    crate::leanh::lean_dec(v_a_4265_);
    crate::leanh::lean_dec_ref(v_a_4264_);
    crate::leanh::lean_dec_ref(v_a_4262_);
    return v_res_4269_;
}
pub unsafe fn _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0()
-> f64 {
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: f64 = 0.0;
    v___x_4270_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4271_ = lean_float_of_nat(v___x_4270_);
    return v___x_4271_;
}
pub unsafe fn l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(
    mut v_e_4274_: *mut crate::leanh::LeanObject,
    mut v_cls_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: f64 = 0.0;
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4276_ = crate::leanh::lean_box(0);
    v___x_4277_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_4278_ = 1;
    v___x_4279_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_4280_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_4280_, 0, v_cls_4275_);
    crate::leanh::lean_ctor_set(v___x_4280_, 1, v___x_4276_);
    crate::leanh::lean_ctor_set(v___x_4280_, 2, v___x_4279_);
    crate::leanh::lean_ctor_set_float(
        v___x_4280_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4277_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_4280_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4277_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4280_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_4278_,
    );
    v___x_4281_ = l_Lean_MessageData_ofExpr(v_e_4274_);
    v___x_4282_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
    v___x_4283_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4283_, 0, v___x_4280_);
    crate::leanh::lean_ctor_set(v___x_4283_, 1, v___x_4281_);
    crate::leanh::lean_ctor_set(v___x_4283_, 2, v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(
    mut v_clsElem_4284_: *mut crate::leanh::LeanObject,
    mut v_sz_4285_: usize,
    mut v_i_4286_: usize,
    mut v_bs_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4288_: u8 = 0;
    let mut v_v_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: usize = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4288_ = lean_usize_dec_lt(v_i_4286_, v_sz_4285_);
                if v___x_4288_ == 0 {
                    crate::leanh::lean_dec(v_clsElem_4284_);
                    return v_bs_4287_;
                } else {
                    v_v_4289_ = lean_array_uget(v_bs_4287_, v_i_4286_);
                    v___x_4290_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4291_ = lean_array_uset(v_bs_4287_, v_i_4286_, v___x_4290_);
                    crate::leanh::lean_inc(v_clsElem_4284_);
                    v___x_4292_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(
                        v_v_4289_,
                        v_clsElem_4284_,
                    );
                    v___x_4293_ = 1usize;
                    v___x_4294_ = lean_usize_add(v_i_4286_, v___x_4293_);
                    v___x_4295_ = lean_array_uset(v_bs_x27_4291_, v_i_4286_, v___x_4292_);
                    v_i_4286_ = v___x_4294_;
                    v_bs_4287_ = v___x_4295_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1___boxed(
    mut v_clsElem_4297_: *mut crate::leanh::LeanObject,
    mut v_sz_4298_: *mut crate::leanh::LeanObject,
    mut v_i_4299_: *mut crate::leanh::LeanObject,
    mut v_bs_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4301_: usize = 0;
    let mut v_i_boxed_4302_: usize = 0;
    let mut v_res_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4301_ = crate::leanh::lean_unbox_usize(v_sz_4298_);
    crate::leanh::lean_dec(v_sz_4298_);
    v_i_boxed_4302_ = crate::leanh::lean_unbox_usize(v_i_4299_);
    crate::leanh::lean_dec(v_i_4299_);
    v_res_4303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_4297_, v_sz_boxed_4301_, v_i_boxed_4302_, v_bs_4300_);
    return v_res_4303_;
}
pub unsafe fn l_Lean_Meta_Grind_ppExprArray(
    mut v_cls_4304_: *mut crate::leanh::LeanObject,
    mut v_header_4305_: *mut crate::leanh::LeanObject,
    mut v_es_4306_: *mut crate::leanh::LeanObject,
    mut v_clsElem_4307_: *mut crate::leanh::LeanObject,
    mut v_collapsed_4308_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4309_: usize = 0;
    let mut v___x_4310_: usize = 0;
    let mut v_es_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: f64 = 0.0;
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4309_ = lean_array_size(v_es_4306_);
    v___x_4310_ = 0usize;
    v_es_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_4307_, v_sz_4309_, v___x_4310_, v_es_4306_);
    v___x_4312_ = crate::leanh::lean_box(0);
    v___x_4313_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_4314_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_4315_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_4315_, 0, v_cls_4304_);
    crate::leanh::lean_ctor_set(v___x_4315_, 1, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4315_, 2, v___x_4314_);
    crate::leanh::lean_ctor_set_float(
        v___x_4315_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4313_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_4315_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4313_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4315_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v_collapsed_4308_,
    );
    v___x_4316_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4316_, 0, v_header_4305_);
    v___x_4317_ = l_Lean_MessageData_ofFormat(v___x_4316_);
    v___x_4318_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4318_, 2, v_es_4311_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_Meta_Grind_ppExprArray___boxed(
    mut v_cls_4319_: *mut crate::leanh::LeanObject,
    mut v_header_4320_: *mut crate::leanh::LeanObject,
    mut v_es_4321_: *mut crate::leanh::LeanObject,
    mut v_clsElem_4322_: *mut crate::leanh::LeanObject,
    mut v_collapsed_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_4324_: u8 = 0;
    let mut v_res_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4324_ = (crate::leanh::lean_unbox(v_collapsed_4323_) as u8);
    v_res_4325_ = l_Lean_Meta_Grind_ppExprArray(
        v_cls_4319_,
        v_header_4320_,
        v_es_4321_,
        v_clsElem_4322_,
        v_collapsed_boxed_4324_,
    );
    return v_res_4325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(
    mut v_declName_4336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    v___x_4337_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1;
    v___x_4338_ = lean_name_eq(v_declName_4336_, v___x_4337_);
    if v___x_4338_ == 0 {
        let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4340_: u8 = 0;
        v___x_4339_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3;
        v___x_4340_ = lean_name_eq(v_declName_4336_, v___x_4339_);
        return v___x_4340_;
    } else {
        return v___x_4338_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___boxed(
    mut v_declName_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: u8 = 0;
    let mut v_r_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_4341_);
    crate::leanh::lean_dec(v_declName_4341_);
    v_r_4343_ = crate::leanh::lean_box((v_res_4342_) as usize);
    return v_r_4343_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(
    mut v_declName_4353_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4355_: u8 = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4358_ =
                    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3;
                v___x_4359_ = lean_name_eq(v_declName_4353_, v___x_4358_);
                if v___x_4359_ == 0 {
                    v___x_4360_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5;
                    v___x_4361_ = lean_name_eq(v_declName_4353_, v___x_4360_);
                    v___y_4355_ = v___x_4361_;
                    state = 1;
                    continue;
                } else {
                    v___y_4355_ = v___x_4359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4355_ == 0 {
                    v___x_4356_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1;
                    v___x_4357_ = lean_name_eq(v_declName_4353_, v___x_4356_);
                    return v___x_4357_;
                } else {
                    return v___y_4355_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(
    mut v_declName_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4363_: u8 = 0;
    let mut v_r_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4363_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_4362_);
    crate::leanh::lean_dec(v_declName_4362_);
    v_r_4364_ = crate::leanh::lean_box((v_res_4363_) as usize);
    return v_r_4364_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(
    mut v_x_4365_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_4365_ {
        0 => {
            let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4366_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4366_;
        }
        1 => {
            let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4367_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4367_;
        }
        _ => {
            let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4368_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4368_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___boxed(
    mut v_x_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4370_: u8 = 0;
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4370_ = (crate::leanh::lean_unbox(v_x_4369_) as u8);
    v_res_4371_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_boxed_4370_);
    return v_res_4371_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(
    mut v_x_4372_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4373_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_4372_);
    return v___x_4373_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx___boxed(
    mut v_x_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4375_: u8 = 0;
    let mut v_res_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4375_ = (crate::leanh::lean_unbox(v_x_4374_) as u8);
    v_res_4376_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(
        v_x_4__boxed_4375_,
    );
    return v_res_4376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(
    mut v_k_4377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4377_);
    return v_k_4377_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(
    mut v_k_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4379_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(
        v_k_4378_,
    );
    crate::leanh::lean_dec(v_k_4378_);
    return v_res_4379_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(
    mut v_motive_4380_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4381_: *mut crate::leanh::LeanObject,
    mut v_t_4382_: u8,
    mut v_h_4383_: *mut crate::leanh::LeanObject,
    mut v_k_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4384_);
    return v_k_4384_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(
    mut v_motive_4385_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4386_: *mut crate::leanh::LeanObject,
    mut v_t_4387_: *mut crate::leanh::LeanObject,
    mut v_h_4388_: *mut crate::leanh::LeanObject,
    mut v_k_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4390_: u8 = 0;
    let mut v_res_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4390_ = (crate::leanh::lean_unbox(v_t_4387_) as u8);
    v_res_4391_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(
        v_motive_4385_,
        v_ctorIdx_4386_,
        v_t_boxed_4390_,
        v_h_4388_,
        v_k_4389_,
    );
    crate::leanh::lean_dec(v_k_4389_);
    crate::leanh::lean_dec(v_ctorIdx_4386_);
    return v_res_4391_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(
    mut v_num_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_num_4392_);
    return v_num_4392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(
    mut v_num_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(
        v_num_4393_,
    );
    crate::leanh::lean_dec(v_num_4393_);
    return v_res_4394_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(
    mut v_motive_4395_: *mut crate::leanh::LeanObject,
    mut v_t_4396_: u8,
    mut v_h_4397_: *mut crate::leanh::LeanObject,
    mut v_num_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_num_4398_);
    return v_num_4398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(
    mut v_motive_4399_: *mut crate::leanh::LeanObject,
    mut v_t_4400_: *mut crate::leanh::LeanObject,
    mut v_h_4401_: *mut crate::leanh::LeanObject,
    mut v_num_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4403_: u8 = 0;
    let mut v_res_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4403_ = (crate::leanh::lean_unbox(v_t_4400_) as u8);
    v_res_4404_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(
        v_motive_4399_,
        v_t_boxed_4403_,
        v_h_4401_,
        v_num_4402_,
    );
    crate::leanh::lean_dec(v_num_4402_);
    return v_res_4404_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(
    mut v_cast_4405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_cast_4405_);
    return v_cast_4405_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(
    mut v_cast_4406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4407_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(
            v_cast_4406_,
        );
    crate::leanh::lean_dec(v_cast_4406_);
    return v_res_4407_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(
    mut v_motive_4408_: *mut crate::leanh::LeanObject,
    mut v_t_4409_: u8,
    mut v_h_4410_: *mut crate::leanh::LeanObject,
    mut v_cast_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_cast_4411_);
    return v_cast_4411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(
    mut v_motive_4412_: *mut crate::leanh::LeanObject,
    mut v_t_4413_: *mut crate::leanh::LeanObject,
    mut v_h_4414_: *mut crate::leanh::LeanObject,
    mut v_cast_4415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4416_: u8 = 0;
    let mut v_res_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4416_ = (crate::leanh::lean_unbox(v_t_4413_) as u8);
    v_res_4417_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(
        v_motive_4412_,
        v_t_boxed_4416_,
        v_h_4414_,
        v_cast_4415_,
    );
    crate::leanh::lean_dec(v_cast_4415_);
    return v_res_4417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(
    mut v_no_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_no_4418_);
    return v_no_4418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(
    mut v_no_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4420_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(
        v_no_4419_,
    );
    crate::leanh::lean_dec(v_no_4419_);
    return v_res_4420_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(
    mut v_motive_4421_: *mut crate::leanh::LeanObject,
    mut v_t_4422_: u8,
    mut v_h_4423_: *mut crate::leanh::LeanObject,
    mut v_no_4424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_no_4424_);
    return v_no_4424_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(
    mut v_motive_4425_: *mut crate::leanh::LeanObject,
    mut v_t_4426_: *mut crate::leanh::LeanObject,
    mut v_h_4427_: *mut crate::leanh::LeanObject,
    mut v_no_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4429_: u8 = 0;
    let mut v_res_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4429_ = (crate::leanh::lean_unbox(v_t_4426_) as u8);
    v_res_4430_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(
        v_motive_4425_,
        v_t_boxed_4429_,
        v_h_4427_,
        v_no_4428_,
    );
    crate::leanh::lean_dec(v_no_4428_);
    return v_res_4430_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedResult_default() -> u8 {
    let mut v___x_4431_: u8 = 0;
    v___x_4431_ = 0;
    return v___x_4431_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult()
-> u8 {
    let mut v___x_4432_: u8 = 0;
    v___x_4432_ = 0;
    return v___x_4432_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(
    mut v_e_4473_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4477_: u8 = 0;
    let mut v_a_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: u8 = 0;
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: u8 = 0;
    let mut v_arg_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: u8 = 0;
    let mut v_arg_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4473_);
                v___x_4484_ = l_Lean_Expr_cleanupAnnotations(v_e_4473_);
                v___x_4485_ = l_Lean_Expr_isApp(v___x_4484_);
                if v___x_4485_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4484_);
                    state = 1;
                    continue;
                } else {
                    v_arg_4486_ = crate::leanh::lean_ctor_get(v___x_4484_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4486_);
                    v___x_4487_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4484_);
                    v___x_4488_ = l_Lean_Expr_isApp(v___x_4487_);
                    if v___x_4488_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4487_);
                        crate::leanh::lean_dec_ref(v_arg_4486_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_4489_ = crate::leanh::lean_ctor_get(v___x_4487_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4489_);
                        v___x_4490_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4487_);
                        v___x_4491_ = l_Lean_Expr_isApp(v___x_4490_);
                        if v___x_4491_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4490_);
                            crate::leanh::lean_dec_ref(v_arg_4489_);
                            crate::leanh::lean_dec_ref(v_arg_4486_);
                            state = 1;
                            continue;
                        } else {
                            v___x_4492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4490_);
                            v___x_4493_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2;
                            v___x_4494_ = l_Lean_Expr_isConstOf(v___x_4492_, v___x_4493_);
                            if v___x_4494_ == 0 {
                                v___x_4495_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5;
                                v___x_4496_ = l_Lean_Expr_isConstOf(v___x_4492_, v___x_4495_);
                                if v___x_4496_ == 0 {
                                    v___x_4497_ = l_Lean_Expr_isApp(v___x_4492_);
                                    if v___x_4497_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_4492_);
                                        crate::leanh::lean_dec_ref(v_arg_4489_);
                                        crate::leanh::lean_dec_ref(v_arg_4486_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_4498_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4492_);
                                        v___x_4499_ = l_Lean_Expr_isApp(v___x_4498_);
                                        if v___x_4499_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_4498_);
                                            crate::leanh::lean_dec_ref(v_arg_4489_);
                                            crate::leanh::lean_dec_ref(v_arg_4486_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_4500_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4498_);
                                            v___x_4501_ = l_Lean_Expr_isApp(v___x_4500_);
                                            if v___x_4501_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_4500_);
                                                crate::leanh::lean_dec_ref(v_arg_4489_);
                                                crate::leanh::lean_dec_ref(v_arg_4486_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4502_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_4500_);
                                                v___x_4503_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8;
                                                v___x_4504_ =
                                                    l_Lean_Expr_isConstOf(v___x_4502_, v___x_4503_);
                                                if v___x_4504_ == 0 {
                                                    v___x_4505_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11;
                                                    v___x_4506_ = l_Lean_Expr_isConstOf(
                                                        v___x_4502_,
                                                        v___x_4505_,
                                                    );
                                                    if v___x_4506_ == 0 {
                                                        v___x_4507_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14;
                                                        v___x_4508_ = l_Lean_Expr_isConstOf(
                                                            v___x_4502_,
                                                            v___x_4507_,
                                                        );
                                                        if v___x_4508_ == 0 {
                                                            v___x_4509_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17;
                                                            v___x_4510_ = l_Lean_Expr_isConstOf(
                                                                v___x_4502_,
                                                                v___x_4509_,
                                                            );
                                                            if v___x_4510_ == 0 {
                                                                v___x_4511_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20;
                                                                v___x_4512_ = l_Lean_Expr_isConstOf(
                                                                    v___x_4502_,
                                                                    v___x_4511_,
                                                                );
                                                                if v___x_4512_ == 0 {
                                                                    v___x_4513_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23;
                                                                    v___x_4514_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_4502_,
                                                                            v___x_4513_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_4502_,
                                                                    );
                                                                    if v___x_4514_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_4489_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_4486_,
                                                                        );
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_4473_,
                                                                        );
                                                                        v_a_4479_ = v_arg_4489_;
                                                                        v_b_4480_ = v_arg_4486_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_4502_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_4473_,
                                                                    );
                                                                    v_a_4479_ = v_arg_4489_;
                                                                    v_b_4480_ = v_arg_4486_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_4502_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_4473_,
                                                                );
                                                                v_a_4479_ = v_arg_4489_;
                                                                v_b_4480_ = v_arg_4486_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_4502_);
                                                            crate::leanh::lean_dec_ref(v_e_4473_);
                                                            v_a_4479_ = v_arg_4489_;
                                                            v_b_4480_ = v_arg_4486_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_4502_);
                                                        crate::leanh::lean_dec_ref(v_e_4473_);
                                                        v_a_4479_ = v_arg_4489_;
                                                        v_b_4480_ = v_arg_4486_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_4502_);
                                                    crate::leanh::lean_dec_ref(v_arg_4486_);
                                                    crate::leanh::lean_dec_ref(v_e_4473_);
                                                    v_e_4473_ = v_arg_4489_;
                                                    state = 0;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4492_);
                                    crate::leanh::lean_dec_ref(v_arg_4489_);
                                    crate::leanh::lean_dec_ref(v_e_4473_);
                                    v_e_4473_ = v_arg_4486_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4492_);
                                crate::leanh::lean_dec_ref(v_arg_4489_);
                                crate::leanh::lean_dec_ref(v_arg_4486_);
                                crate::leanh::lean_dec_ref(v_e_4473_);
                                v___x_4517_ = 0;
                                return v___x_4517_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4475_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_4473_);
                crate::leanh::lean_dec_ref(v_e_4473_);
                if v___x_4475_ == 0 {
                    v___x_4476_ = 2;
                    return v___x_4476_;
                } else {
                    v___x_4477_ = 1;
                    return v___x_4477_;
                }
            }
            2 => {
                v___x_4481_ =
                    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(
                        v_a_4479_,
                    );
                match v___x_4481_ {
                    0 => {
                        v___x_4482_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_4480_);
                        if v___x_4482_ == 0 {
                            return v___x_4482_;
                        } else {
                            return v___x_4482_;
                        }
                    }
                    1 => {
                        v___x_4483_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_4480_);
                        match v___x_4483_ {
                            2 => {
                                return v___x_4483_;
                            }
                            1 => {
                                return v___x_4483_;
                            }
                            _ => {
                                return v___x_4481_;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_b_4480_);
                        return v___x_4481_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(
    mut v_e_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4519_: u8 = 0;
    let mut v_r_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4519_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_4518_);
    v_r_4520_ = crate::leanh::lean_box((v_res_4519_) as usize);
    return v_r_4520_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(
    mut v_e_4521_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4522_: u8 = 0;
    v___x_4522_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_4521_);
    if v___x_4522_ == 1 {
        let mut v___x_4523_: u8 = 0;
        v___x_4523_ = 1;
        return v___x_4523_;
    } else {
        let mut v___x_4524_: u8 = 0;
        v___x_4524_ = 0;
        return v___x_4524_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(
    mut v_e_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: u8 = 0;
    let mut v_r_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_4525_);
    v_r_4527_ = crate::leanh::lean_box((v_res_4526_) as usize);
    return v_r_4527_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(
    mut v_declName_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = lean_st_ref_get(v___y_4529_);
    v_env_4532_ = crate::leanh::lean_ctor_get(v___x_4531_, 0);
    crate::leanh::lean_inc_ref(v_env_4532_);
    crate::leanh::lean_dec(v___x_4531_);
    v___x_4533_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4532_, v_declName_4528_);
    v___x_4534_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4533_);
    return v___x_4534_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(
    mut v_declName_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4538_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(
            v_declName_4535_,
            v___y_4536_,
        );
    crate::leanh::lean_dec(v___y_4536_);
    return v_res_4538_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(
    mut v_declName_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(
            v_declName_4539_,
            v___y_4543_,
        );
    return v___x_4545_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(
    mut v_declName_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(
        v_declName_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
        v___y_4550_,
    );
    crate::leanh::lean_dec(v___y_4550_);
    crate::leanh::lean_dec_ref(v___y_4549_);
    crate::leanh::lean_dec(v___y_4548_);
    crate::leanh::lean_dec_ref(v___y_4547_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Meta_Grind_isSupportApp(
    mut v_e_4553_: *mut crate::leanh::LeanObject,
    mut v_a_4554_: *mut crate::leanh::LeanObject,
    mut v_a_4555_: *mut crate::leanh::LeanObject,
    mut v_a_4556_: *mut crate::leanh::LeanObject,
    mut v_a_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: u8 = 0;
    let mut v_env_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: u8 = 0;
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4592_: u8 = 0;
    let mut v___x_4593_: u8 = 0;
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4553_);
                v___x_4559_ =
                    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(
                        v_e_4553_,
                    );
                v___x_4560_ = 1;
                if v___x_4559_ == 0 {
                    v___x_4561_ = l_Lean_Expr_getAppFn(v_e_4553_);
                    if crate::leanh::lean_obj_tag(v___x_4561_) == 4 {
                        v_declName_4562_ = crate::leanh::lean_ctor_get(v___x_4561_, 0);
                        crate::leanh::lean_inc_n(v_declName_4562_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4561_, 2);
                        v___x_4579_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_4562_, v_a_4557_);
                        v_a_4580_ = crate::leanh::lean_ctor_get(v___x_4579_, 0);
                        crate::leanh::lean_inc(v_a_4580_);
                        crate::leanh::lean_dec_ref(v___x_4579_);
                        if crate::leanh::lean_obj_tag(v_a_4580_) == 1 {
                            v_val_4581_ = crate::leanh::lean_ctor_get(v_a_4580_, 0);
                            crate::leanh::lean_inc(v_val_4581_);
                            crate::leanh::lean_dec_ref_known(v_a_4580_, 1);
                            v_numParams_4582_ = crate::leanh::lean_ctor_get(v_val_4581_, 1);
                            crate::leanh::lean_inc(v_numParams_4582_);
                            crate::leanh::lean_dec(v_val_4581_);
                            v___x_4583_ = l_Lean_Expr_getAppNumArgs(v_e_4553_);
                            v___x_4584_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4585_ = lean_nat_add(v_numParams_4582_, v___x_4584_);
                            crate::leanh::lean_dec(v_numParams_4582_);
                            v___x_4586_ = lean_nat_dec_eq(v___x_4583_, v___x_4585_);
                            crate::leanh::lean_dec(v___x_4585_);
                            crate::leanh::lean_dec(v___x_4583_);
                            if v___x_4586_ == 0 {
                                crate::leanh::lean_dec_ref(v_e_4553_);
                                v___y_4564_ = v_a_4557_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4587_ = l_Lean_Expr_appArg_x21(v_e_4553_);
                                crate::leanh::lean_dec_ref(v_e_4553_);
                                v___x_4588_ = l_Lean_Meta_isConstructorApp(
                                    v___x_4587_,
                                    v_a_4554_,
                                    v_a_4555_,
                                    v_a_4556_,
                                    v_a_4557_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4588_) == 0 {
                                    v_a_4589_ = crate::leanh::lean_ctor_get(v___x_4588_, 0);
                                    v_isSharedCheck_4598_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4588_)) as u8;
                                    if v_isSharedCheck_4598_ == 0 {
                                        v___x_4591_ = v___x_4588_;
                                        v_isShared_4592_ = v_isSharedCheck_4598_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4589_);
                                        crate::leanh::lean_dec(v___x_4588_);
                                        v___x_4591_ = crate::leanh::lean_box(0);
                                        v_isShared_4592_ = v_isSharedCheck_4598_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_declName_4562_);
                                    return v___x_4588_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4580_);
                            crate::leanh::lean_dec_ref(v_e_4553_);
                            v___y_4564_ = v_a_4557_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4561_);
                        crate::leanh::lean_dec_ref(v_e_4553_);
                        v___x_4599_ = crate::leanh::lean_box((v___x_4559_) as usize);
                        v___x_4600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4600_, 0, v___x_4599_);
                        return v___x_4600_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4553_);
                    v___x_4601_ = crate::leanh::lean_box((v___x_4560_) as usize);
                    v___x_4602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4602_, 0, v___x_4601_);
                    return v___x_4602_;
                }
            }
            1 => {
                v___x_4565_ = lean_st_ref_get(v___y_4564_);
                v___x_4566_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_4562_);
                if v___x_4566_ == 0 {
                    v___x_4567_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(
                        v_declName_4562_,
                    );
                    if v___x_4567_ == 0 {
                        v___x_4568_ =
                            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(
                                v_declName_4562_,
                            );
                        if v___x_4568_ == 0 {
                            v_env_4569_ = crate::leanh::lean_ctor_get(v___x_4565_, 0);
                            crate::leanh::lean_inc_ref(v_env_4569_);
                            crate::leanh::lean_dec(v___x_4565_);
                            v___x_4570_ = lean_is_matcher(v_env_4569_, v_declName_4562_);
                            v___x_4571_ = crate::leanh::lean_box((v___x_4570_) as usize);
                            v___x_4572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4572_, 0, v___x_4571_);
                            return v___x_4572_;
                        } else {
                            crate::leanh::lean_dec(v___x_4565_);
                            crate::leanh::lean_dec(v_declName_4562_);
                            v___x_4573_ = crate::leanh::lean_box((v___x_4560_) as usize);
                            v___x_4574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4574_, 0, v___x_4573_);
                            return v___x_4574_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4565_);
                        crate::leanh::lean_dec(v_declName_4562_);
                        v___x_4575_ = crate::leanh::lean_box((v___x_4560_) as usize);
                        v___x_4576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4576_, 0, v___x_4575_);
                        return v___x_4576_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4565_);
                    crate::leanh::lean_dec(v_declName_4562_);
                    v___x_4577_ = crate::leanh::lean_box((v___x_4560_) as usize);
                    v___x_4578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4578_, 0, v___x_4577_);
                    return v___x_4578_;
                }
            }
            2 => {
                v___x_4593_ = (crate::leanh::lean_unbox(v_a_4589_) as u8);
                crate::leanh::lean_dec(v_a_4589_);
                if v___x_4593_ == 0 {
                    crate::leanh::lean_del_object(v___x_4591_);
                    v___y_4564_ = v_a_4557_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_4562_);
                    v___x_4594_ = crate::leanh::lean_box((v___x_4560_) as usize);
                    if v_isShared_4592_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4591_, 0, v___x_4594_);
                        v___x_4596_ = v___x_4591_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
                        v___x_4596_ = v_reuseFailAlloc_4597_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isSupportApp___boxed(
    mut v_e_4603_: *mut crate::leanh::LeanObject,
    mut v_a_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_a_4606_: *mut crate::leanh::LeanObject,
    mut v_a_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ =
        l_Lean_Meta_Grind_isSupportApp(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
    crate::leanh::lean_dec(v_a_4607_);
    crate::leanh::lean_dec_ref(v_a_4606_);
    crate::leanh::lean_dec(v_a_4605_);
    crate::leanh::lean_dec_ref(v_a_4604_);
    return v_res_4609_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(
    mut v_a_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4610_) == 0 {
                    v___x_4612_ = l_List_reverse___redArg(v_a_4611_);
                    return v___x_4612_;
                } else {
                    v_head_4613_ = crate::leanh::lean_ctor_get(v_a_4610_, 0);
                    v_tail_4614_ = crate::leanh::lean_ctor_get(v_a_4610_, 1);
                    v_isSharedCheck_4623_ = (!crate::leanh::lean_is_exclusive(v_a_4610_)) as u8;
                    if v_isSharedCheck_4623_ == 0 {
                        v___x_4616_ = v_a_4610_;
                        v_isShared_4617_ = v_isSharedCheck_4623_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4614_);
                        crate::leanh::lean_inc(v_head_4613_);
                        crate::leanh::lean_dec(v_a_4610_);
                        v___x_4616_ = crate::leanh::lean_box(0);
                        v_isShared_4617_ = v_isSharedCheck_4623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4618_ = l_Lean_MessageData_ofExpr(v_head_4613_);
                if v_isShared_4617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4616_, 1, v_a_4611_);
                    crate::leanh::lean_ctor_set(v___x_4616_, 0, v___x_4618_);
                    v___x_4620_ = v___x_4616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4622_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_a_4611_);
                    v___x_4620_ = v_reuseFailAlloc_4622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4610_ = v_tail_4614_;
                v_a_4611_ = v___x_4620_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_ppEqc___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: u8 = 0;
    let mut v___x_4629_: f64 = 0.0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_4628_ = 1;
    v___x_4629_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_4630_ = crate::leanh::lean_box(0);
    v___x_4631_ = l_Lean_Meta_Grind_ppEqc___closed__1;
    v___x_4632_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_4632_, 0, v___x_4631_);
    crate::leanh::lean_ctor_set(v___x_4632_, 1, v___x_4630_);
    crate::leanh::lean_ctor_set(v___x_4632_, 2, v___x_4627_);
    crate::leanh::lean_ctor_set_float(
        v___x_4632_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4629_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_4632_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4629_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4632_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_4628_,
    );
    return v___x_4632_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ppEqc___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Lean_Meta_Grind_ppEqc___closed__4;
    v___x_4637_ = l_Lean_MessageData_ofFormat(v___x_4636_);
    return v___x_4637_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ppEqc___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
    v___x_4639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__5_once),
        _init_l_Lean_Meta_Grind_ppEqc___closed__5,
    );
    v___x_4640_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4640_, 0, v___x_4639_);
    crate::leanh::lean_ctor_set(v___x_4640_, 1, v___x_4638_);
    return v___x_4640_;
}
pub unsafe fn l_Lean_Meta_Grind_ppEqc(
    mut v_eqc_4641_: *mut crate::leanh::LeanObject,
    mut v_children_4642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__2_once),
        _init_l_Lean_Meta_Grind_ppEqc___closed__2,
    );
    v___x_4644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
    v___x_4645_ = crate::leanh::lean_box(0);
    v___x_4646_ =
        l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(v_eqc_4641_, v___x_4645_);
    v___x_4647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ppEqc___closed__6_once),
        _init_l_Lean_Meta_Grind_ppEqc___closed__6,
    );
    v___x_4648_ = l_Lean_MessageData_joinSep(v___x_4646_, v___x_4647_);
    v___x_4649_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4649_, 0, v___x_4644_);
    crate::leanh::lean_ctor_set(v___x_4649_, 1, v___x_4648_);
    v___x_4650_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
    v___x_4651_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4651_, 0, v___x_4649_);
    crate::leanh::lean_ctor_set(v___x_4651_, 1, v___x_4650_);
    v___x_4652_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4652_, 0, v___x_4651_);
    v___x_4653_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4653_, 0, v___x_4643_);
    crate::leanh::lean_ctor_set(v___x_4653_, 1, v___x_4652_);
    crate::leanh::lean_ctor_set(v___x_4653_, 2, v_children_4642_);
    return v___x_4653_;
}
pub unsafe fn l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(
    mut v_a_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4661_: u8 = 0;
    let mut v___x_4662_: u8 = 0;
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4654_) == 0 {
                    v___x_4656_ = l_List_reverse___redArg(v_a_4655_);
                    return v___x_4656_;
                } else {
                    v_head_4657_ = crate::leanh::lean_ctor_get(v_a_4654_, 0);
                    v_tail_4658_ = crate::leanh::lean_ctor_get(v_a_4654_, 1);
                    v_isSharedCheck_4668_ = (!crate::leanh::lean_is_exclusive(v_a_4654_)) as u8;
                    if v_isSharedCheck_4668_ == 0 {
                        v___x_4660_ = v_a_4654_;
                        v_isShared_4661_ = v_isSharedCheck_4668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4658_);
                        crate::leanh::lean_inc(v_head_4657_);
                        crate::leanh::lean_dec(v_a_4654_);
                        v___x_4660_ = crate::leanh::lean_box(0);
                        v_isShared_4661_ = v_isSharedCheck_4668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_4657_);
                v___x_4662_ = l_Lean_Expr_isTrue(v_head_4657_);
                if v___x_4662_ == 0 {
                    if v_isShared_4661_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4660_, 1, v_a_4655_);
                        v___x_4664_ = v___x_4660_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4666_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_head_4657_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_a_4655_);
                        v___x_4664_ = v_reuseFailAlloc_4666_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4660_);
                    crate::leanh::lean_dec(v_head_4657_);
                    v_a_4654_ = v_tail_4658_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_4654_ = v_tail_4658_;
                v_a_4655_ = v___x_4664_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(
    mut v_a_4669_: *mut crate::leanh::LeanObject,
    mut v_a_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4669_) == 0 {
                    v___x_4671_ = l_List_reverse___redArg(v_a_4670_);
                    return v___x_4671_;
                } else {
                    v_head_4672_ = crate::leanh::lean_ctor_get(v_a_4669_, 0);
                    v_tail_4673_ = crate::leanh::lean_ctor_get(v_a_4669_, 1);
                    v_isSharedCheck_4683_ = (!crate::leanh::lean_is_exclusive(v_a_4669_)) as u8;
                    if v_isSharedCheck_4683_ == 0 {
                        v___x_4675_ = v_a_4669_;
                        v_isShared_4676_ = v_isSharedCheck_4683_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4673_);
                        crate::leanh::lean_inc(v_head_4672_);
                        crate::leanh::lean_dec(v_a_4669_);
                        v___x_4675_ = crate::leanh::lean_box(0);
                        v_isShared_4676_ = v_isSharedCheck_4683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_4672_);
                v___x_4677_ = l_Lean_Expr_isFalse(v_head_4672_);
                if v___x_4677_ == 0 {
                    if v_isShared_4676_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4675_, 1, v_a_4670_);
                        v___x_4679_ = v___x_4675_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4681_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_head_4672_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 1, v_a_4670_);
                        v___x_4679_ = v_reuseFailAlloc_4681_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4675_);
                    crate::leanh::lean_dec(v_head_4672_);
                    v_a_4669_ = v_tail_4673_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_4669_ = v_tail_4673_;
                v_a_4670_ = v___x_4679_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(
    mut v_x_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4684_) == 0 {
                    v___x_4685_ = crate::leanh::lean_box(0);
                    return v___x_4685_;
                } else {
                    v_head_4686_ = crate::leanh::lean_ctor_get(v_x_4684_, 0);
                    crate::leanh::lean_inc_n(v_head_4686_, 2);
                    v_tail_4687_ = crate::leanh::lean_ctor_get(v_x_4684_, 1);
                    crate::leanh::lean_inc(v_tail_4687_);
                    crate::leanh::lean_dec_ref_known(v_x_4684_, 2);
                    v___x_4688_ = l_Lean_Expr_isTrue(v_head_4686_);
                    if v___x_4688_ == 0 {
                        crate::leanh::lean_dec(v_head_4686_);
                        v_x_4684_ = v_tail_4687_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4687_);
                        v___x_4690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4690_, 0, v_head_4686_);
                        return v___x_4690_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(
    mut v_x_4691_: *mut crate::leanh::LeanObject,
    mut v_x_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4717_: u8 = 0;
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4691_) == 0 {
                    v___x_4699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4699_, 0, v_x_4692_);
                    crate::leanh::lean_ctor_set(v___x_4699_, 1, v___y_4693_);
                    v___x_4700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4700_, 0, v___x_4699_);
                    return v___x_4700_;
                } else {
                    v_head_4701_ = crate::leanh::lean_ctor_get(v_x_4691_, 0);
                    v_tail_4702_ = crate::leanh::lean_ctor_get(v_x_4691_, 1);
                    v_isSharedCheck_4722_ = (!crate::leanh::lean_is_exclusive(v_x_4691_)) as u8;
                    if v_isSharedCheck_4722_ == 0 {
                        v___x_4704_ = v_x_4691_;
                        v_isShared_4705_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4702_);
                        crate::leanh::lean_inc(v_head_4701_);
                        crate::leanh::lean_dec(v_x_4691_);
                        v___x_4704_ = crate::leanh::lean_box(0);
                        v_isShared_4705_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_4701_);
                v___x_4706_ = l_Lean_Meta_Grind_isSupportApp(
                    v_head_4701_,
                    v___y_4694_,
                    v___y_4695_,
                    v___y_4696_,
                    v___y_4697_,
                );
                if crate::leanh::lean_obj_tag(v___x_4706_) == 0 {
                    v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4706_, 0);
                    crate::leanh::lean_inc(v_a_4707_);
                    crate::leanh::lean_dec_ref_known(v___x_4706_, 1);
                    v___x_4708_ = (crate::leanh::lean_unbox(v_a_4707_) as u8);
                    crate::leanh::lean_dec(v_a_4707_);
                    if v___x_4708_ == 0 {
                        crate::leanh::lean_del_object(v___x_4704_);
                        crate::leanh::lean_dec(v_head_4701_);
                        v_x_4691_ = v_tail_4702_;
                        state = 0;
                        continue;
                    } else {
                        if v_isShared_4705_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4704_, 1, v_x_4692_);
                            v___x_4711_ = v___x_4704_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4713_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_head_4701_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 1, v_x_4692_);
                            v___x_4711_ = v_reuseFailAlloc_4713_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4704_);
                    crate::leanh::lean_dec(v_tail_4702_);
                    crate::leanh::lean_dec(v_head_4701_);
                    crate::leanh::lean_dec_ref(v___y_4693_);
                    crate::leanh::lean_dec(v_x_4692_);
                    v_a_4714_ = crate::leanh::lean_ctor_get(v___x_4706_, 0);
                    v_isSharedCheck_4721_ = (!crate::leanh::lean_is_exclusive(v___x_4706_)) as u8;
                    if v_isSharedCheck_4721_ == 0 {
                        v___x_4716_ = v___x_4706_;
                        v_isShared_4717_ = v_isSharedCheck_4721_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4714_);
                        crate::leanh::lean_dec(v___x_4706_);
                        v___x_4716_ = crate::leanh::lean_box(0);
                        v_isShared_4717_ = v_isSharedCheck_4721_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4691_ = v_tail_4702_;
                v_x_4692_ = v___x_4711_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4717_ == 0 {
                    v___x_4719_ = v___x_4716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
                    v___x_4719_ = v_reuseFailAlloc_4720_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg___boxed(
    mut v_x_4723_: *mut crate::leanh::LeanObject,
    mut v_x_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4731_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_4723_, v_x_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
    crate::leanh::lean_dec(v___y_4729_);
    crate::leanh::lean_dec_ref(v___y_4728_);
    crate::leanh::lean_dec(v___y_4727_);
    crate::leanh::lean_dec_ref(v___y_4726_);
    return v_res_4731_;
}
pub unsafe fn l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(
    mut v_x_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4732_) == 0 {
                    v___x_4733_ = crate::leanh::lean_box(0);
                    return v___x_4733_;
                } else {
                    v_head_4734_ = crate::leanh::lean_ctor_get(v_x_4732_, 0);
                    crate::leanh::lean_inc_n(v_head_4734_, 2);
                    v_tail_4735_ = crate::leanh::lean_ctor_get(v_x_4732_, 1);
                    crate::leanh::lean_inc(v_tail_4735_);
                    crate::leanh::lean_dec_ref_known(v_x_4732_, 2);
                    v___x_4736_ = l_Lean_Expr_isFalse(v_head_4734_);
                    if v___x_4736_ == 0 {
                        crate::leanh::lean_dec(v_head_4734_);
                        v_x_4732_ = v_tail_4735_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4735_);
                        v___x_4738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4738_, 0, v_head_4734_);
                        return v___x_4738_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(
    mut v_a_4739_: u8,
    mut v_x_4740_: *mut crate::leanh::LeanObject,
    mut v_x_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: u8 = 0;
    let mut v_a_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4740_) == 0 {
                    v___x_4748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4748_, 0, v_x_4741_);
                    crate::leanh::lean_ctor_set(v___x_4748_, 1, v___y_4742_);
                    v___x_4749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4749_, 0, v___x_4748_);
                    return v___x_4749_;
                } else {
                    v_head_4750_ = crate::leanh::lean_ctor_get(v_x_4740_, 0);
                    v_tail_4751_ = crate::leanh::lean_ctor_get(v_x_4740_, 1);
                    v_isSharedCheck_4773_ = (!crate::leanh::lean_is_exclusive(v_x_4740_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4753_ = v_x_4740_;
                        v_isShared_4754_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4751_);
                        crate::leanh::lean_inc(v_head_4750_);
                        crate::leanh::lean_dec(v_x_4740_);
                        v___x_4753_ = crate::leanh::lean_box(0);
                        v_isShared_4754_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_4750_);
                v___x_4755_ = l_Lean_Meta_Grind_isSupportApp(
                    v_head_4750_,
                    v___y_4743_,
                    v___y_4744_,
                    v___y_4745_,
                    v___y_4746_,
                );
                if crate::leanh::lean_obj_tag(v___x_4755_) == 0 {
                    v_a_4756_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                    crate::leanh::lean_inc(v_a_4756_);
                    crate::leanh::lean_dec_ref_known(v___x_4755_, 1);
                    v___x_4763_ = (crate::leanh::lean_unbox(v_a_4756_) as u8);
                    crate::leanh::lean_dec(v_a_4756_);
                    if v___x_4763_ == 0 {
                        v_snd_4758_ = v___y_4742_;
                        state = 2;
                        continue;
                    } else {
                        if v_a_4739_ == 0 {
                            crate::leanh::lean_del_object(v___x_4753_);
                            crate::leanh::lean_dec(v_head_4750_);
                            v_x_4740_ = v_tail_4751_;
                            state = 0;
                            continue;
                        } else {
                            v_snd_4758_ = v___y_4742_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4753_);
                    crate::leanh::lean_dec(v_tail_4751_);
                    crate::leanh::lean_dec(v_head_4750_);
                    crate::leanh::lean_dec_ref(v___y_4742_);
                    crate::leanh::lean_dec(v_x_4741_);
                    v_a_4765_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                    v_isSharedCheck_4772_ = (!crate::leanh::lean_is_exclusive(v___x_4755_)) as u8;
                    if v_isSharedCheck_4772_ == 0 {
                        v___x_4767_ = v___x_4755_;
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4765_);
                        crate::leanh::lean_dec(v___x_4755_);
                        v___x_4767_ = crate::leanh::lean_box(0);
                        v_isShared_4768_ = v_isSharedCheck_4772_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4753_, 1, v_x_4741_);
                    v___x_4760_ = v___x_4753_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_head_4750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_x_4741_);
                    v___x_4760_ = v_reuseFailAlloc_4762_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_4740_ = v_tail_4751_;
                v_x_4741_ = v___x_4760_;
                v___y_4742_ = v_snd_4758_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4768_ == 0 {
                    v___x_4770_ = v___x_4767_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
                    v___x_4770_ = v_reuseFailAlloc_4771_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(
    mut v_a_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_20243__boxed_4783_: u8 = 0;
    let mut v_res_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_20243__boxed_4783_ = (crate::leanh::lean_unbox(v_a_4774_) as u8);
    v_res_4784_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_a_20243__boxed_4783_, v_x_4775_, v_x_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
    crate::leanh::lean_dec(v___y_4781_);
    crate::leanh::lean_dec_ref(v___y_4780_);
    crate::leanh::lean_dec(v___y_4779_);
    crate::leanh::lean_dec_ref(v___y_4778_);
    return v_res_4784_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(
    mut v_collapsedProps_4790_: u8,
    mut v_as_x27_4791_: *mut crate::leanh::LeanObject,
    mut v_b_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4809_: u8 = 0;
    let mut v_fst_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v_fst_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v___y_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: u8 = 0;
    let mut v_regularEqcs_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: u8 = 0;
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4882_: u8 = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4906_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4918_: u8 = 0;
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4921_: u8 = 0;
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4941_: u8 = 0;
    let mut v_unused_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_unused_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v_unused_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut v_unused_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4791_) == 0 {
                    v___x_4800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4800_, 0, v_b_4792_);
                    crate::leanh::lean_ctor_set(v___x_4800_, 1, v___y_4794_);
                    v___x_4801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4801_, 0, v___x_4800_);
                    return v___x_4801_;
                } else {
                    v_snd_4802_ = crate::leanh::lean_ctor_get(v_b_4792_, 1);
                    crate::leanh::lean_inc(v_snd_4802_);
                    v_snd_4803_ = crate::leanh::lean_ctor_get(v_snd_4802_, 1);
                    crate::leanh::lean_inc(v_snd_4803_);
                    v_head_4804_ = crate::leanh::lean_ctor_get(v_as_x27_4791_, 0);
                    v_tail_4805_ = crate::leanh::lean_ctor_get(v_as_x27_4791_, 1);
                    v_fst_4806_ = crate::leanh::lean_ctor_get(v_b_4792_, 0);
                    v_isSharedCheck_4970_ = (!crate::leanh::lean_is_exclusive(v_b_4792_)) as u8;
                    if v_isSharedCheck_4970_ == 0 {
                        v_unused_4971_ = crate::leanh::lean_ctor_get(v_b_4792_, 1);
                        crate::leanh::lean_dec(v_unused_4971_);
                        v___x_4808_ = v_b_4792_;
                        v_isShared_4809_ = v_isSharedCheck_4970_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4806_);
                        crate::leanh::lean_dec(v_b_4792_);
                        v___x_4808_ = crate::leanh::lean_box(0);
                        v_isShared_4809_ = v_isSharedCheck_4970_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4810_ = crate::leanh::lean_ctor_get(v_snd_4802_, 0);
                v_isSharedCheck_4968_ = (!crate::leanh::lean_is_exclusive(v_snd_4802_)) as u8;
                if v_isSharedCheck_4968_ == 0 {
                    v_unused_4969_ = crate::leanh::lean_ctor_get(v_snd_4802_, 1);
                    crate::leanh::lean_dec(v_unused_4969_);
                    v___x_4812_ = v_snd_4802_;
                    v_isShared_4813_ = v_isSharedCheck_4968_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4810_);
                    crate::leanh::lean_dec(v_snd_4802_);
                    v___x_4812_ = crate::leanh::lean_box(0);
                    v_isShared_4813_ = v_isSharedCheck_4968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4814_ = crate::leanh::lean_ctor_get(v_snd_4803_, 0);
                v_snd_4815_ = crate::leanh::lean_ctor_get(v_snd_4803_, 1);
                v_isSharedCheck_4967_ = (!crate::leanh::lean_is_exclusive(v_snd_4803_)) as u8;
                if v_isSharedCheck_4967_ == 0 {
                    v___x_4817_ = v_snd_4803_;
                    v_isShared_4818_ = v_isSharedCheck_4967_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4815_);
                    crate::leanh::lean_inc(v_fst_4814_);
                    crate::leanh::lean_dec(v_snd_4803_);
                    v___x_4817_ = crate::leanh::lean_box(0);
                    v_isShared_4818_ = v_isSharedCheck_4967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_head_4804_);
                v___x_4831_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_head_4804_);
                if crate::leanh::lean_obj_tag(v___x_4831_) == 0 {
                    crate::leanh::lean_inc(v_head_4804_);
                    v___x_4832_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(v_head_4804_);
                    if crate::leanh::lean_obj_tag(v___x_4832_) == 0 {
                        if crate::leanh::lean_obj_tag(v_head_4804_) == 1 {
                            v_tail_4833_ = crate::leanh::lean_ctor_get(v_head_4804_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_4833_) == 1 {
                                crate::leanh::lean_del_object(v___x_4817_);
                                crate::leanh::lean_del_object(v___x_4812_);
                                crate::leanh::lean_del_object(v___x_4808_);
                                v_head_4834_ = crate::leanh::lean_ctor_get(v_head_4804_, 0);
                                crate::leanh::lean_inc(v_head_4834_);
                                v___x_4835_ = l_Lean_Meta_isProof(
                                    v_head_4834_,
                                    v___y_4795_,
                                    v___y_4796_,
                                    v___y_4797_,
                                    v___y_4798_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4835_) == 0 {
                                    v_a_4836_ = crate::leanh::lean_ctor_get(v___x_4835_, 0);
                                    crate::leanh::lean_inc(v_a_4836_);
                                    crate::leanh::lean_dec_ref_known(v___x_4835_, 1);
                                    v___x_4837_ = (crate::leanh::lean_unbox(v_a_4836_) as u8);
                                    if v___x_4837_ == 0 {
                                        v_regularEqcs_4838_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                                        v___x_4889_ = crate::leanh::lean_box(0);
                                        v___x_4890_ = (crate::leanh::lean_unbox(v_a_4836_) as u8);
                                        crate::leanh::lean_dec(v_a_4836_);
                                        crate::leanh::lean_inc_ref(v_head_4804_);
                                        v___x_4891_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v___x_4890_, v_head_4804_, v___x_4889_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
                                        if crate::leanh::lean_obj_tag(v___x_4891_) == 0 {
                                            v_a_4892_ = crate::leanh::lean_ctor_get(v___x_4891_, 0);
                                            crate::leanh::lean_inc(v_a_4892_);
                                            crate::leanh::lean_dec_ref_known(v___x_4891_, 1);
                                            v_fst_4893_ = crate::leanh::lean_ctor_get(v_a_4892_, 0);
                                            crate::leanh::lean_inc(v_fst_4893_);
                                            v_snd_4894_ = crate::leanh::lean_ctor_get(v_a_4892_, 1);
                                            crate::leanh::lean_inc(v_snd_4894_);
                                            crate::leanh::lean_dec(v_a_4892_);
                                            v___x_4895_ = l_List_reverse___redArg(v_fst_4893_);
                                            v_fst_4861_ = v___x_4895_;
                                            v_snd_4862_ = v_snd_4894_;
                                            state = 9;
                                            continue;
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_4891_) == 0 {
                                                v_a_4896_ =
                                                    crate::leanh::lean_ctor_get(v___x_4891_, 0);
                                                crate::leanh::lean_inc(v_a_4896_);
                                                crate::leanh::lean_dec_ref_known(v___x_4891_, 1);
                                                v_fst_4897_ =
                                                    crate::leanh::lean_ctor_get(v_a_4896_, 0);
                                                crate::leanh::lean_inc(v_fst_4897_);
                                                v_snd_4898_ =
                                                    crate::leanh::lean_ctor_get(v_a_4896_, 1);
                                                crate::leanh::lean_inc(v_snd_4898_);
                                                crate::leanh::lean_dec(v_a_4896_);
                                                v_fst_4861_ = v_fst_4897_;
                                                v_snd_4862_ = v_snd_4898_;
                                                state = 9;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_snd_4815_);
                                                crate::leanh::lean_dec(v_fst_4814_);
                                                crate::leanh::lean_dec(v_fst_4810_);
                                                crate::leanh::lean_dec(v_fst_4806_);
                                                v_a_4899_ =
                                                    crate::leanh::lean_ctor_get(v___x_4891_, 0);
                                                v_isSharedCheck_4906_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4891_))
                                                        as u8;
                                                if v_isSharedCheck_4906_ == 0 {
                                                    v___x_4901_ = v___x_4891_;
                                                    v_isShared_4902_ = v_isSharedCheck_4906_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4899_);
                                                    crate::leanh::lean_dec(v___x_4891_);
                                                    v___x_4901_ = crate::leanh::lean_box(0);
                                                    v_isShared_4902_ = v_isSharedCheck_4906_;
                                                    state = 12;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4836_);
                                        v___x_4907_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4907_, 0, v_fst_4814_);
                                        crate::leanh::lean_ctor_set(v___x_4907_, 1, v_snd_4815_);
                                        v___x_4908_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4908_, 0, v_fst_4810_);
                                        crate::leanh::lean_ctor_set(v___x_4908_, 1, v___x_4907_);
                                        v___x_4909_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4909_, 0, v_fst_4806_);
                                        crate::leanh::lean_ctor_set(v___x_4909_, 1, v___x_4908_);
                                        v_as_x27_4791_ = v_tail_4805_;
                                        v_b_4792_ = v___x_4909_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_4815_);
                                    crate::leanh::lean_dec(v_fst_4814_);
                                    crate::leanh::lean_dec(v_fst_4810_);
                                    crate::leanh::lean_dec(v_fst_4806_);
                                    crate::leanh::lean_dec_ref(v___y_4794_);
                                    v_a_4911_ = crate::leanh::lean_ctor_get(v___x_4835_, 0);
                                    v_isSharedCheck_4918_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4835_)) as u8;
                                    if v_isSharedCheck_4918_ == 0 {
                                        v___x_4913_ = v___x_4835_;
                                        v_isShared_4914_ = v_isSharedCheck_4918_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4911_);
                                        crate::leanh::lean_dec(v___x_4835_);
                                        v___x_4913_ = crate::leanh::lean_box(0);
                                        v_isShared_4914_ = v_isSharedCheck_4918_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_4820_ = v___y_4794_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_4820_ = v___y_4794_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4817_);
                        crate::leanh::lean_del_object(v___x_4812_);
                        crate::leanh::lean_del_object(v___x_4808_);
                        v_isSharedCheck_4941_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4832_)) as u8;
                        if v_isSharedCheck_4941_ == 0 {
                            v_unused_4942_ = crate::leanh::lean_ctor_get(v___x_4832_, 0);
                            crate::leanh::lean_dec(v_unused_4942_);
                            v___x_4920_ = v___x_4832_;
                            v_isShared_4921_ = v_isSharedCheck_4941_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4832_);
                            v___x_4920_ = crate::leanh::lean_box(0);
                            v_isShared_4921_ = v_isSharedCheck_4941_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4817_);
                    crate::leanh::lean_del_object(v___x_4812_);
                    crate::leanh::lean_del_object(v___x_4808_);
                    v_isSharedCheck_4965_ = (!crate::leanh::lean_is_exclusive(v___x_4831_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v_unused_4966_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                        crate::leanh::lean_dec(v_unused_4966_);
                        v___x_4944_ = v___x_4831_;
                        v_isShared_4945_ = v_isSharedCheck_4965_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4831_);
                        v___x_4944_ = crate::leanh::lean_box(0);
                        v_isShared_4945_ = v_isSharedCheck_4965_;
                        state = 18;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4818_ == 0 {
                    v___x_4822_ = v___x_4817_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_fst_4814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_snd_4815_);
                    v___x_4822_ = v_reuseFailAlloc_4830_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4812_, 1, v___x_4822_);
                    v___x_4824_ = v___x_4812_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4829_, 1, v___x_4822_);
                    v___x_4824_ = v_reuseFailAlloc_4829_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4809_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4808_, 1, v___x_4824_);
                    v___x_4826_ = v___x_4808_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 1, v___x_4824_);
                    v___x_4826_ = v_reuseFailAlloc_4828_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_as_x27_4791_ = v_tail_4805_;
                v_b_4792_ = v___x_4826_;
                v___y_4794_ = v___y_4820_;
                state = 0;
                continue;
            }
            8 => {
                v___x_4843_ = l_List_isEmpty___redArg(v_fst_4841_);
                if v___x_4843_ == 0 {
                    v___x_4844_ = l_Lean_Meta_Grind_ppEqc(v_fst_4841_, v_regularEqcs_4838_);
                    v___x_4845_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4846_ = lean_mk_empty_array_with_capacity(v___x_4845_);
                    v___x_4847_ = lean_array_push(v___x_4846_, v___x_4844_);
                    v___x_4848_ = l_Lean_Meta_Grind_ppEqc(v___y_4840_, v___x_4847_);
                    v___x_4849_ = lean_array_push(v_fst_4814_, v___x_4848_);
                    v___x_4850_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4849_);
                    crate::leanh::lean_ctor_set(v___x_4850_, 1, v_snd_4815_);
                    v___x_4851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4851_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v___x_4851_, 1, v___x_4850_);
                    v___x_4852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4852_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v___x_4852_, 1, v___x_4851_);
                    v_as_x27_4791_ = v_tail_4805_;
                    v_b_4792_ = v___x_4852_;
                    v___y_4794_ = v_snd_4842_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_4841_);
                    v___x_4854_ = l_Lean_Meta_Grind_ppEqc(v___y_4840_, v_regularEqcs_4838_);
                    v___x_4855_ = lean_array_push(v_fst_4814_, v___x_4854_);
                    v___x_4856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4856_, 0, v___x_4855_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 1, v_snd_4815_);
                    v___x_4857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4857_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v___x_4857_, 1, v___x_4856_);
                    v___x_4858_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4858_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v___x_4858_, 1, v___x_4857_);
                    v_as_x27_4791_ = v_tail_4805_;
                    v_b_4792_ = v___x_4858_;
                    v___y_4794_ = v_snd_4842_;
                    state = 0;
                    continue;
                }
            }
            9 => {
                v___x_4863_ = l_List_lengthTR___redArg(v_fst_4861_);
                v___x_4864_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4865_ = lean_nat_dec_le(v___x_4863_, v___x_4864_);
                crate::leanh::lean_dec(v___x_4863_);
                if v___x_4865_ == 0 {
                    v___x_4866_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_head_4804_);
                    v___x_4867_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_head_4804_, v___x_4866_, v_snd_4862_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
                    if crate::leanh::lean_obj_tag(v___x_4867_) == 0 {
                        v_a_4868_ = crate::leanh::lean_ctor_get(v___x_4867_, 0);
                        crate::leanh::lean_inc(v_a_4868_);
                        crate::leanh::lean_dec_ref_known(v___x_4867_, 1);
                        v_fst_4869_ = crate::leanh::lean_ctor_get(v_a_4868_, 0);
                        crate::leanh::lean_inc(v_fst_4869_);
                        v_snd_4870_ = crate::leanh::lean_ctor_get(v_a_4868_, 1);
                        crate::leanh::lean_inc(v_snd_4870_);
                        crate::leanh::lean_dec(v_a_4868_);
                        v___x_4871_ = l_List_reverse___redArg(v_fst_4869_);
                        v___y_4840_ = v_fst_4861_;
                        v_fst_4841_ = v___x_4871_;
                        v_snd_4842_ = v_snd_4870_;
                        state = 8;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4867_) == 0 {
                            v_a_4872_ = crate::leanh::lean_ctor_get(v___x_4867_, 0);
                            crate::leanh::lean_inc(v_a_4872_);
                            crate::leanh::lean_dec_ref_known(v___x_4867_, 1);
                            v_fst_4873_ = crate::leanh::lean_ctor_get(v_a_4872_, 0);
                            crate::leanh::lean_inc(v_fst_4873_);
                            v_snd_4874_ = crate::leanh::lean_ctor_get(v_a_4872_, 1);
                            crate::leanh::lean_inc(v_snd_4874_);
                            crate::leanh::lean_dec(v_a_4872_);
                            v___y_4840_ = v_fst_4861_;
                            v_fst_4841_ = v_fst_4873_;
                            v_snd_4842_ = v_snd_4874_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_4861_);
                            crate::leanh::lean_dec(v_snd_4815_);
                            crate::leanh::lean_dec(v_fst_4814_);
                            crate::leanh::lean_dec(v_fst_4810_);
                            crate::leanh::lean_dec(v_fst_4806_);
                            v_a_4875_ = crate::leanh::lean_ctor_get(v___x_4867_, 0);
                            v_isSharedCheck_4882_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4867_)) as u8;
                            if v_isSharedCheck_4882_ == 0 {
                                v___x_4877_ = v___x_4867_;
                                v_isShared_4878_ = v_isSharedCheck_4882_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4875_);
                                crate::leanh::lean_dec(v___x_4867_);
                                v___x_4877_ = crate::leanh::lean_box(0);
                                v_isShared_4878_ = v_isSharedCheck_4882_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4861_);
                    crate::leanh::lean_inc_ref(v_head_4804_);
                    v___x_4883_ = l_Lean_Meta_Grind_ppEqc(v_head_4804_, v_regularEqcs_4838_);
                    v___x_4884_ = lean_array_push(v_snd_4815_, v___x_4883_);
                    v___x_4885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4885_, 0, v_fst_4814_);
                    crate::leanh::lean_ctor_set(v___x_4885_, 1, v___x_4884_);
                    v___x_4886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4886_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v___x_4886_, 1, v___x_4885_);
                    v___x_4887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4887_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v___x_4887_, 1, v___x_4886_);
                    v_as_x27_4791_ = v_tail_4805_;
                    v_b_4792_ = v___x_4887_;
                    v___y_4794_ = v_snd_4862_;
                    state = 0;
                    continue;
                }
            }
            10 => {
                if v_isShared_4878_ == 0 {
                    v___x_4880_ = v___x_4877_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
                    v___x_4880_ = v_reuseFailAlloc_4881_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4880_;
            }
            12 => {
                if v_isShared_4902_ == 0 {
                    v___x_4904_ = v___x_4901_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
                    v___x_4904_ = v_reuseFailAlloc_4905_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4904_;
            }
            14 => {
                if v_isShared_4914_ == 0 {
                    v___x_4916_ = v___x_4913_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
                    v___x_4916_ = v_reuseFailAlloc_4917_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4916_;
            }
            16 => {
                v___x_4922_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_head_4804_);
                v___x_4923_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(v_head_4804_, v___x_4922_);
                v___x_4924_ = l_List_isEmpty___redArg(v___x_4923_);
                if v___x_4924_ == 0 {
                    crate::leanh::lean_dec(v_fst_4810_);
                    v___x_4925_ = l_Lean_Meta_Grind_ppEqc___closed__1;
                    v___x_4926_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0;
                    v___x_4927_ = lean_array_mk(v___x_4923_);
                    v___x_4928_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2;
                    v___x_4929_ = l_Lean_Meta_Grind_ppExprArray(
                        v___x_4925_,
                        v___x_4926_,
                        v___x_4927_,
                        v___x_4928_,
                        v_collapsedProps_4790_,
                    );
                    if v_isShared_4921_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4920_, 0, v___x_4929_);
                        v___x_4931_ = v___x_4920_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4929_);
                        v___x_4931_ = v_reuseFailAlloc_4936_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4923_);
                    crate::leanh::lean_del_object(v___x_4920_);
                    v___x_4937_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4937_, 0, v_fst_4814_);
                    crate::leanh::lean_ctor_set(v___x_4937_, 1, v_snd_4815_);
                    v___x_4938_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4938_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v___x_4938_, 1, v___x_4937_);
                    v___x_4939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4939_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v___x_4939_, 1, v___x_4938_);
                    v_as_x27_4791_ = v_tail_4805_;
                    v_b_4792_ = v___x_4939_;
                    state = 0;
                    continue;
                }
            }
            17 => {
                v___x_4932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4932_, 0, v_fst_4814_);
                crate::leanh::lean_ctor_set(v___x_4932_, 1, v_snd_4815_);
                v___x_4933_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4933_, 0, v___x_4931_);
                crate::leanh::lean_ctor_set(v___x_4933_, 1, v___x_4932_);
                v___x_4934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4934_, 0, v_fst_4806_);
                crate::leanh::lean_ctor_set(v___x_4934_, 1, v___x_4933_);
                v_as_x27_4791_ = v_tail_4805_;
                v_b_4792_ = v___x_4934_;
                state = 0;
                continue;
            }
            18 => {
                v___x_4946_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_head_4804_);
                v___x_4947_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(v_head_4804_, v___x_4946_);
                v___x_4948_ = l_List_isEmpty___redArg(v___x_4947_);
                if v___x_4948_ == 0 {
                    crate::leanh::lean_dec(v_fst_4806_);
                    v___x_4949_ = l_Lean_Meta_Grind_ppEqc___closed__1;
                    v___x_4950_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3;
                    v___x_4951_ = lean_array_mk(v___x_4947_);
                    v___x_4952_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2;
                    v___x_4953_ = l_Lean_Meta_Grind_ppExprArray(
                        v___x_4949_,
                        v___x_4950_,
                        v___x_4951_,
                        v___x_4952_,
                        v_collapsedProps_4790_,
                    );
                    if v_isShared_4945_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4944_, 0, v___x_4953_);
                        v___x_4955_ = v___x_4944_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_4960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4953_);
                        v___x_4955_ = v_reuseFailAlloc_4960_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4947_);
                    crate::leanh::lean_del_object(v___x_4944_);
                    v___x_4961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4961_, 0, v_fst_4814_);
                    crate::leanh::lean_ctor_set(v___x_4961_, 1, v_snd_4815_);
                    v___x_4962_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4962_, 0, v_fst_4810_);
                    crate::leanh::lean_ctor_set(v___x_4962_, 1, v___x_4961_);
                    v___x_4963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4963_, 0, v_fst_4806_);
                    crate::leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
                    v_as_x27_4791_ = v_tail_4805_;
                    v_b_4792_ = v___x_4963_;
                    state = 0;
                    continue;
                }
            }
            19 => {
                v___x_4956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4956_, 0, v_fst_4814_);
                crate::leanh::lean_ctor_set(v___x_4956_, 1, v_snd_4815_);
                v___x_4957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4957_, 0, v_fst_4810_);
                crate::leanh::lean_ctor_set(v___x_4957_, 1, v___x_4956_);
                v___x_4958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4958_, 0, v___x_4955_);
                crate::leanh::lean_ctor_set(v___x_4958_, 1, v___x_4957_);
                v_as_x27_4791_ = v_tail_4805_;
                v_b_4792_ = v___x_4958_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___boxed(
    mut v_collapsedProps_4972_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4973_: *mut crate::leanh::LeanObject,
    mut v_b_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
    mut v___y_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsedProps_boxed_4982_: u8 = 0;
    let mut v_res_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsedProps_boxed_4982_ = (crate::leanh::lean_unbox(v_collapsedProps_4972_) as u8);
    v_res_4983_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_boxed_4982_, v_as_x27_4973_, v_b_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
    crate::leanh::lean_dec(v___y_4980_);
    crate::leanh::lean_dec_ref(v___y_4979_);
    crate::leanh::lean_dec(v___y_4978_);
    crate::leanh::lean_dec_ref(v___y_4977_);
    crate::leanh::lean_dec_ref(v___y_4975_);
    crate::leanh::lean_dec(v_as_x27_4973_);
    return v_res_4983_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: u8 = 0;
    let mut v___x_4986_: f64 = 0.0;
    let mut v_trueEqc_x3f_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4984_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_4985_ = 1;
    v___x_4986_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v_trueEqc_x3f_4987_ = crate::leanh::lean_box(0);
    v___x_4988_ = l_Lean_Meta_Grind_ppEqc___closed__1;
    v___x_4989_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_4989_, 0, v___x_4988_);
    crate::leanh::lean_ctor_set(v___x_4989_, 1, v_trueEqc_x3f_4987_);
    crate::leanh::lean_ctor_set(v___x_4989_, 2, v___x_4984_);
    crate::leanh::lean_ctor_set_float(
        v___x_4989_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4986_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_4989_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4986_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4989_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_4985_,
    );
    return v___x_4989_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4993_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2;
    v___x_4994_ = l_Lean_MessageData_ofFormat(v___x_4993_);
    return v___x_4994_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5006_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8;
    v___x_5007_ = l_Lean_MessageData_ofFormat(v___x_5006_);
    return v___x_5007_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(
    mut v_collapsedProps_5008_: u8,
    mut v_a_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
    mut v_a_5011_: *mut crate::leanh::LeanObject,
    mut v_a_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___y_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_regularEqcs_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5065_: u8 = 0;
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5016_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5017_ = 1;
                v___x_5030_ = l_Lean_Meta_Grind_Goal_getEqcs(v_a_5009_, v___x_5017_);
                v___x_5031_ =
                    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6;
                v___x_5032_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_5008_, v___x_5030_, v___x_5031_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
                crate::leanh::lean_dec(v___x_5030_);
                if crate::leanh::lean_obj_tag(v___x_5032_) == 0 {
                    v_a_5033_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                    crate::leanh::lean_inc(v_a_5033_);
                    crate::leanh::lean_dec_ref_known(v___x_5032_, 1);
                    v_fst_5034_ = crate::leanh::lean_ctor_get(v_a_5033_, 0);
                    crate::leanh::lean_inc(v_fst_5034_);
                    v_snd_5035_ = crate::leanh::lean_ctor_get(v_fst_5034_, 1);
                    crate::leanh::lean_inc(v_snd_5035_);
                    v_snd_5036_ = crate::leanh::lean_ctor_get(v_a_5033_, 1);
                    crate::leanh::lean_inc(v_snd_5036_);
                    crate::leanh::lean_dec(v_a_5033_);
                    v_fst_5037_ = crate::leanh::lean_ctor_get(v_fst_5034_, 0);
                    crate::leanh::lean_inc(v_fst_5037_);
                    crate::leanh::lean_dec(v_fst_5034_);
                    v_fst_5038_ = crate::leanh::lean_ctor_get(v_snd_5035_, 0);
                    crate::leanh::lean_inc(v_fst_5038_);
                    v_snd_5039_ = crate::leanh::lean_ctor_get(v_snd_5035_, 1);
                    crate::leanh::lean_inc(v_snd_5039_);
                    crate::leanh::lean_dec(v_snd_5035_);
                    v_fst_5054_ = crate::leanh::lean_ctor_get(v_snd_5039_, 0);
                    crate::leanh::lean_inc(v_fst_5054_);
                    v_snd_5055_ = crate::leanh::lean_ctor_get(v_snd_5039_, 1);
                    crate::leanh::lean_inc(v_snd_5055_);
                    crate::leanh::lean_dec(v_snd_5039_);
                    v___x_5056_ = lean_array_get_size(v_snd_5055_);
                    v___x_5057_ = lean_nat_dec_eq(v___x_5056_, v___x_5016_);
                    if v___x_5057_ == 0 {
                        v___x_5058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
                        v___x_5059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9);
                        v___x_5060_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5060_, 0, v___x_5058_);
                        crate::leanh::lean_ctor_set(v___x_5060_, 1, v___x_5059_);
                        crate::leanh::lean_ctor_set(v___x_5060_, 2, v_snd_5055_);
                        v___x_5061_ = lean_array_push(v_fst_5054_, v___x_5060_);
                        v_regularEqcs_5048_ = v___x_5061_;
                        v___y_5049_ = v_snd_5036_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_5055_);
                        v_regularEqcs_5048_ = v_fst_5054_;
                        v___y_5049_ = v_snd_5036_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5062_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                    v_isSharedCheck_5069_ = (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                    if v_isSharedCheck_5069_ == 0 {
                        v___x_5064_ = v___x_5032_;
                        v_isShared_5065_ = v_isSharedCheck_5069_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5062_);
                        crate::leanh::lean_dec(v___x_5032_);
                        v___x_5064_ = crate::leanh::lean_box(0);
                        v_isShared_5065_ = v_isSharedCheck_5069_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5021_ = lean_array_get_size(v___y_5019_);
                v___x_5022_ = lean_nat_dec_eq(v___x_5021_, v___x_5016_);
                if v___x_5022_ == 0 {
                    v___x_5023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
                    v___x_5024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3);
                    v___x_5025_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5025_, 0, v___x_5023_);
                    crate::leanh::lean_ctor_set(v___x_5025_, 1, v___x_5024_);
                    crate::leanh::lean_ctor_set(v___x_5025_, 2, v___y_5019_);
                    v___x_5026_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v___x_5025_,
                            v___y_5020_,
                        );
                    return v___x_5026_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5019_);
                    v___x_5027_ = crate::leanh::lean_box(0);
                    v___x_5028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5028_, 0, v___x_5027_);
                    crate::leanh::lean_ctor_set(v___x_5028_, 1, v___y_5020_);
                    v___x_5029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5029_, 0, v___x_5028_);
                    return v___x_5029_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_5038_) == 1 {
                    v_val_5043_ = crate::leanh::lean_ctor_get(v_fst_5038_, 0);
                    crate::leanh::lean_inc(v_val_5043_);
                    crate::leanh::lean_dec_ref_known(v_fst_5038_, 1);
                    v___x_5044_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5043_,
                            v___y_5042_,
                        );
                    v_a_5045_ = crate::leanh::lean_ctor_get(v___x_5044_, 0);
                    crate::leanh::lean_inc(v_a_5045_);
                    crate::leanh::lean_dec_ref(v___x_5044_);
                    v_snd_5046_ = crate::leanh::lean_ctor_get(v_a_5045_, 1);
                    crate::leanh::lean_inc(v_snd_5046_);
                    crate::leanh::lean_dec(v_a_5045_);
                    v___y_5019_ = v___y_5041_;
                    v___y_5020_ = v_snd_5046_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5038_);
                    v___y_5019_ = v___y_5041_;
                    v___y_5020_ = v___y_5042_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_fst_5037_) == 1 {
                    v_val_5050_ = crate::leanh::lean_ctor_get(v_fst_5037_, 0);
                    crate::leanh::lean_inc(v_val_5050_);
                    crate::leanh::lean_dec_ref_known(v_fst_5037_, 1);
                    v___x_5051_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5050_,
                            v___y_5049_,
                        );
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    crate::leanh::lean_inc(v_a_5052_);
                    crate::leanh::lean_dec_ref(v___x_5051_);
                    v_snd_5053_ = crate::leanh::lean_ctor_get(v_a_5052_, 1);
                    crate::leanh::lean_inc(v_snd_5053_);
                    crate::leanh::lean_dec(v_a_5052_);
                    v___y_5041_ = v_regularEqcs_5048_;
                    v___y_5042_ = v_snd_5053_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5037_);
                    v___y_5041_ = v_regularEqcs_5048_;
                    v___y_5042_ = v___y_5049_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_5065_ == 0 {
                    v___x_5067_ = v___x_5064_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
                    v___x_5067_ = v_reuseFailAlloc_5068_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(
    mut v_collapsedProps_5070_: *mut crate::leanh::LeanObject,
    mut v_a_5071_: *mut crate::leanh::LeanObject,
    mut v_a_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
    mut v_a_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
    mut v_a_5076_: *mut crate::leanh::LeanObject,
    mut v_a_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsedProps_boxed_5078_: u8 = 0;
    let mut v_res_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsedProps_boxed_5078_ = (crate::leanh::lean_unbox(v_collapsedProps_5070_) as u8);
    v_res_5079_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(
        v_collapsedProps_boxed_5078_,
        v_a_5071_,
        v_a_5072_,
        v_a_5073_,
        v_a_5074_,
        v_a_5075_,
        v_a_5076_,
    );
    crate::leanh::lean_dec(v_a_5076_);
    crate::leanh::lean_dec_ref(v_a_5075_);
    crate::leanh::lean_dec(v_a_5074_);
    crate::leanh::lean_dec_ref(v_a_5073_);
    crate::leanh::lean_dec_ref(v_a_5071_);
    return v_res_5079_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(
    mut v_x_5080_: *mut crate::leanh::LeanObject,
    mut v_x_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
    mut v___y_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
    mut v___y_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_5080_, v_x_5081_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
    return v___x_5089_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(
    mut v_x_5090_: *mut crate::leanh::LeanObject,
    mut v_x_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
    mut v___y_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5099_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_x_5090_, v_x_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
    crate::leanh::lean_dec(v___y_5097_);
    crate::leanh::lean_dec_ref(v___y_5096_);
    crate::leanh::lean_dec(v___y_5095_);
    crate::leanh::lean_dec_ref(v___y_5094_);
    crate::leanh::lean_dec_ref(v___y_5092_);
    return v_res_5099_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(
    mut v_a_5100_: u8,
    mut v_x_5101_: *mut crate::leanh::LeanObject,
    mut v_x_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5110_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_a_5100_, v_x_5101_, v_x_5102_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
    return v___x_5110_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(
    mut v_a_5111_: *mut crate::leanh::LeanObject,
    mut v_x_5112_: *mut crate::leanh::LeanObject,
    mut v_x_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_20916__boxed_5121_: u8 = 0;
    let mut v_res_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_20916__boxed_5121_ = (crate::leanh::lean_unbox(v_a_5111_) as u8);
    v_res_5122_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(v_a_20916__boxed_5121_, v_x_5112_, v_x_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
    crate::leanh::lean_dec(v___y_5119_);
    crate::leanh::lean_dec_ref(v___y_5118_);
    crate::leanh::lean_dec(v___y_5117_);
    crate::leanh::lean_dec_ref(v___y_5116_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    return v_res_5122_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(
    mut v_collapsedProps_5123_: u8,
    mut v_as_5124_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5125_: *mut crate::leanh::LeanObject,
    mut v_b_5126_: *mut crate::leanh::LeanObject,
    mut v_a_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_5123_, v_as_x27_5125_, v_b_5126_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
    return v___x_5135_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___boxed(
    mut v_collapsedProps_5136_: *mut crate::leanh::LeanObject,
    mut v_as_5137_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5138_: *mut crate::leanh::LeanObject,
    mut v_b_5139_: *mut crate::leanh::LeanObject,
    mut v_a_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsedProps_boxed_5148_: u8 = 0;
    let mut v_res_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsedProps_boxed_5148_ = (crate::leanh::lean_unbox(v_collapsedProps_5136_) as u8);
    v_res_5149_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(v_collapsedProps_boxed_5148_, v_as_5137_, v_as_x27_5138_, v_b_5139_, v_a_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_);
    crate::leanh::lean_dec(v___y_5146_);
    crate::leanh::lean_dec_ref(v___y_5145_);
    crate::leanh::lean_dec(v___y_5144_);
    crate::leanh::lean_dec_ref(v___y_5143_);
    crate::leanh::lean_dec_ref(v___y_5141_);
    crate::leanh::lean_dec(v_as_x27_5138_);
    crate::leanh::lean_dec(v_as_5137_);
    return v_res_5149_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(
    mut v_a_5150_: *mut crate::leanh::LeanObject,
    mut v_a_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5157_: u8 = 0;
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5150_) == 0 {
                    v___x_5152_ = l_List_reverse___redArg(v_a_5151_);
                    return v___x_5152_;
                } else {
                    v_head_5153_ = crate::leanh::lean_ctor_get(v_a_5150_, 0);
                    v_tail_5154_ = crate::leanh::lean_ctor_get(v_a_5150_, 1);
                    v_isSharedCheck_5163_ = (!crate::leanh::lean_is_exclusive(v_a_5150_)) as u8;
                    if v_isSharedCheck_5163_ == 0 {
                        v___x_5156_ = v_a_5150_;
                        v_isShared_5157_ = v_isSharedCheck_5163_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5154_);
                        crate::leanh::lean_inc(v_head_5153_);
                        crate::leanh::lean_dec(v_a_5150_);
                        v___x_5156_ = crate::leanh::lean_box(0);
                        v_isShared_5157_ = v_isSharedCheck_5163_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5158_ = l_Lean_Meta_Grind_ppPattern(v_head_5153_);
                if v_isShared_5157_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5156_, 1, v_a_5151_);
                    crate::leanh::lean_ctor_set(v___x_5156_, 0, v___x_5158_);
                    v___x_5160_ = v___x_5156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5162_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_a_5151_);
                    v___x_5160_ = v_reuseFailAlloc_5162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5150_ = v_tail_5154_;
                v_a_5151_ = v___x_5160_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(
    mut v_a_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5171_: u8 = 0;
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5164_) == 0 {
                    v___x_5166_ = l_List_reverse___redArg(v_a_5165_);
                    return v___x_5166_;
                } else {
                    v_head_5167_ = crate::leanh::lean_ctor_get(v_a_5164_, 0);
                    v_tail_5168_ = crate::leanh::lean_ctor_get(v_a_5164_, 1);
                    v_isSharedCheck_5176_ = (!crate::leanh::lean_is_exclusive(v_a_5164_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5170_ = v_a_5164_;
                        v_isShared_5171_ = v_isSharedCheck_5176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5168_);
                        crate::leanh::lean_inc(v_head_5167_);
                        crate::leanh::lean_dec(v_a_5164_);
                        v___x_5170_ = crate::leanh::lean_box(0);
                        v_isShared_5171_ = v_isSharedCheck_5176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5170_, 1, v_a_5165_);
                    v___x_5173_ = v___x_5170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_head_5167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_a_5165_);
                    v___x_5173_ = v_reuseFailAlloc_5175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5164_ = v_tail_5168_;
                v_a_5165_ = v___x_5173_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5178_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0;
    v___x_5179_ = l_Lean_stringToMessageData(v___x_5178_);
    return v___x_5179_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5185_: f64 = 0.0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5183_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_5184_ = 1;
    v___x_5185_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_5186_ = crate::leanh::lean_box(0);
    v___x_5187_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3;
    v___x_5188_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_5188_, 0, v___x_5187_);
    crate::leanh::lean_ctor_set(v___x_5188_, 1, v___x_5186_);
    crate::leanh::lean_ctor_set(v___x_5188_, 2, v___x_5183_);
    crate::leanh::lean_ctor_set_float(
        v___x_5188_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5185_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_5188_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_5185_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5188_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_5184_,
    );
    return v___x_5188_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(
    mut v_thm_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_patterns_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_patterns_5191_ = crate::leanh::lean_ctor_get(v_thm_5189_, 3);
    crate::leanh::lean_inc(v_patterns_5191_);
    v_origin_5192_ = crate::leanh::lean_ctor_get(v_thm_5189_, 5);
    crate::leanh::lean_inc_ref(v_origin_5192_);
    crate::leanh::lean_dec_ref(v_thm_5189_);
    v___x_5193_ = l_Lean_Meta_Grind_Origin_pp(v_origin_5192_);
    v___x_5194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1);
    v___x_5195_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5195_, 0, v___x_5193_);
    crate::leanh::lean_ctor_set(v___x_5195_, 1, v___x_5194_);
    v___x_5196_ = crate::leanh::lean_box(0);
    v___x_5197_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(v_patterns_5191_, v___x_5196_);
    v___x_5198_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(v___x_5197_, v___x_5196_);
    v___x_5199_ = l_Lean_MessageData_ofList(v___x_5198_);
    v_m_5200_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_m_5200_, 0, v___x_5195_);
    crate::leanh::lean_ctor_set(v_m_5200_, 1, v___x_5199_);
    v___x_5201_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4);
    v___x_5202_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
    v___x_5203_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5203_, 0, v___x_5201_);
    crate::leanh::lean_ctor_set(v___x_5203_, 1, v_m_5200_);
    crate::leanh::lean_ctor_set(v___x_5203_, 2, v___x_5202_);
    v___x_5204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5204_, 0, v___x_5203_);
    return v___x_5204_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(
    mut v_thm_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5207_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(
        v_thm_5205_,
    );
    return v_res_5207_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(
    mut v_thm_5208_: *mut crate::leanh::LeanObject,
    mut v_a_5209_: *mut crate::leanh::LeanObject,
    mut v_a_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(
        v_thm_5208_,
    );
    return v___x_5214_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(
    mut v_thm_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
    mut v_a_5218_: *mut crate::leanh::LeanObject,
    mut v_a_5219_: *mut crate::leanh::LeanObject,
    mut v_a_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(
        v_thm_5215_,
        v_a_5216_,
        v_a_5217_,
        v_a_5218_,
        v_a_5219_,
    );
    crate::leanh::lean_dec(v_a_5219_);
    crate::leanh::lean_dec_ref(v_a_5218_);
    crate::leanh::lean_dec(v_a_5217_);
    crate::leanh::lean_dec_ref(v_a_5216_);
    return v_res_5221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(
    mut v_sz_5222_: usize,
    mut v_i_5223_: usize,
    mut v_bs_5224_: *mut crate::leanh::LeanObject,
    mut v___y_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5227_: u8 = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: usize = 0;
    let mut v___x_5236_: usize = 0;
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5227_ = lean_usize_dec_lt(v_i_5223_, v_sz_5222_);
                if v___x_5227_ == 0 {
                    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5228_, 0, v_bs_5224_);
                    crate::leanh::lean_ctor_set(v___x_5228_, 1, v___y_5225_);
                    v___x_5229_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5229_, 0, v___x_5228_);
                    return v___x_5229_;
                } else {
                    v_v_5230_ = lean_array_uget_borrowed(v_bs_5224_, v_i_5223_);
                    crate::leanh::lean_inc(v_v_5230_);
                    v___x_5231_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_v_5230_);
                    if crate::leanh::lean_obj_tag(v___x_5231_) == 0 {
                        v_a_5232_ = crate::leanh::lean_ctor_get(v___x_5231_, 0);
                        crate::leanh::lean_inc(v_a_5232_);
                        crate::leanh::lean_dec_ref_known(v___x_5231_, 1);
                        v___x_5233_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5234_ = lean_array_uset(v_bs_5224_, v_i_5223_, v___x_5233_);
                        v___x_5235_ = 1usize;
                        v___x_5236_ = lean_usize_add(v_i_5223_, v___x_5235_);
                        v___x_5237_ = lean_array_uset(v_bs_x27_5234_, v_i_5223_, v_a_5232_);
                        v_i_5223_ = v___x_5236_;
                        v_bs_5224_ = v___x_5237_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_5225_);
                        crate::leanh::lean_dec_ref(v_bs_5224_);
                        v_a_5239_ = crate::leanh::lean_ctor_get(v___x_5231_, 0);
                        v_isSharedCheck_5246_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5231_)) as u8;
                        if v_isSharedCheck_5246_ == 0 {
                            v___x_5241_ = v___x_5231_;
                            v_isShared_5242_ = v_isSharedCheck_5246_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5239_);
                            crate::leanh::lean_dec(v___x_5231_);
                            v___x_5241_ = crate::leanh::lean_box(0);
                            v_isShared_5242_ = v_isSharedCheck_5246_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5242_ == 0 {
                    v___x_5244_ = v___x_5241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
                    v___x_5244_ = v_reuseFailAlloc_5245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(
    mut v_sz_5247_: *mut crate::leanh::LeanObject,
    mut v_i_5248_: *mut crate::leanh::LeanObject,
    mut v_bs_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5252_: usize = 0;
    let mut v_i_boxed_5253_: usize = 0;
    let mut v_res_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5252_ = crate::leanh::lean_unbox_usize(v_sz_5247_);
    crate::leanh::lean_dec(v_sz_5247_);
    v_i_boxed_5253_ = crate::leanh::lean_unbox_usize(v_i_5248_);
    crate::leanh::lean_dec(v_i_5248_);
    v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_boxed_5252_, v_i_boxed_5253_, v_bs_5249_, v___y_5250_);
    return v_res_5254_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: f64 = 0.0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_5259_ = 1;
    v___x_5260_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_5261_ = crate::leanh::lean_box(0);
    v___x_5262_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1;
    v___x_5263_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_5263_, 0, v___x_5262_);
    crate::leanh::lean_ctor_set(v___x_5263_, 1, v___x_5261_);
    crate::leanh::lean_ctor_set(v___x_5263_, 2, v___x_5258_);
    crate::leanh::lean_ctor_set_float(
        v___x_5263_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5260_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_5263_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_5260_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5263_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_5259_,
    );
    return v___x_5263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5267_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4;
    v___x_5268_ = l_Lean_MessageData_ofFormat(v___x_5267_);
    return v___x_5268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(
    mut v_a_5269_: *mut crate::leanh::LeanObject,
    mut v_a_5270_: *mut crate::leanh::LeanObject,
    mut v_a_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newThms_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5281_: usize = 0;
    let mut v___x_5282_: usize = 0;
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5288_: usize = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v_fst_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5314_: u8 = 0;
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut v_a_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5323_: u8 = 0;
    let mut v_a_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_5276_ = crate::leanh::lean_ctor_get(v_a_5269_, 0);
                v_ematch_5277_ = crate::leanh::lean_ctor_get(v_toGoalState_5276_, 12);
                v_thms_5278_ = crate::leanh::lean_ctor_get(v_ematch_5277_, 2);
                v_newThms_5279_ = crate::leanh::lean_ctor_get(v_ematch_5277_, 3);
                v___x_5280_ = l_Lean_PersistentArray_toArray___redArg(v_thms_5278_);
                v_sz_5281_ = lean_array_size(v___x_5280_);
                v___x_5282_ = 0usize;
                v___x_5283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_5281_, v___x_5282_, v___x_5280_, v_a_5270_);
                if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                    v_a_5284_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                    crate::leanh::lean_inc(v_a_5284_);
                    crate::leanh::lean_dec_ref_known(v___x_5283_, 1);
                    v_fst_5285_ = crate::leanh::lean_ctor_get(v_a_5284_, 0);
                    crate::leanh::lean_inc(v_fst_5285_);
                    v_snd_5286_ = crate::leanh::lean_ctor_get(v_a_5284_, 1);
                    crate::leanh::lean_inc(v_snd_5286_);
                    crate::leanh::lean_dec(v_a_5284_);
                    v___x_5287_ = l_Lean_PersistentArray_toArray___redArg(v_newThms_5279_);
                    v_sz_5288_ = lean_array_size(v___x_5287_);
                    v___x_5289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_5288_, v___x_5282_, v___x_5287_, v_snd_5286_);
                    if crate::leanh::lean_obj_tag(v___x_5289_) == 0 {
                        v_a_5290_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                        v_isSharedCheck_5315_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                        if v_isSharedCheck_5315_ == 0 {
                            v___x_5292_ = v___x_5289_;
                            v_isShared_5293_ = v_isSharedCheck_5315_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5290_);
                            crate::leanh::lean_dec(v___x_5289_);
                            v___x_5292_ = crate::leanh::lean_box(0);
                            v_isShared_5293_ = v_isSharedCheck_5315_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5285_);
                        v_a_5316_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                        v_isSharedCheck_5323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                        if v_isSharedCheck_5323_ == 0 {
                            v___x_5318_ = v___x_5289_;
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5316_);
                            crate::leanh::lean_dec(v___x_5289_);
                            v___x_5318_ = crate::leanh::lean_box(0);
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_5324_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                    v_isSharedCheck_5331_ = (!crate::leanh::lean_is_exclusive(v___x_5283_)) as u8;
                    if v_isSharedCheck_5331_ == 0 {
                        v___x_5326_ = v___x_5283_;
                        v_isShared_5327_ = v_isSharedCheck_5331_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5324_);
                        crate::leanh::lean_dec(v___x_5283_);
                        v___x_5326_ = crate::leanh::lean_box(0);
                        v_isShared_5327_ = v_isSharedCheck_5331_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5294_ = crate::leanh::lean_ctor_get(v_a_5290_, 0);
                v_snd_5295_ = crate::leanh::lean_ctor_get(v_a_5290_, 1);
                v_isSharedCheck_5314_ = (!crate::leanh::lean_is_exclusive(v_a_5290_)) as u8;
                if v_isSharedCheck_5314_ == 0 {
                    v___x_5297_ = v_a_5290_;
                    v_isShared_5298_ = v_isSharedCheck_5314_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5295_);
                    crate::leanh::lean_inc(v_fst_5294_);
                    crate::leanh::lean_dec(v_a_5290_);
                    v___x_5297_ = crate::leanh::lean_box(0);
                    v_isShared_5298_ = v_isSharedCheck_5314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5299_ = l_Array_append___redArg(v_fst_5285_, v_fst_5294_);
                crate::leanh::lean_dec(v_fst_5294_);
                v___x_5300_ = lean_array_get_size(v___x_5299_);
                v___x_5301_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5302_ = lean_nat_dec_eq(v___x_5300_, v___x_5301_);
                if v___x_5302_ == 0 {
                    crate::leanh::lean_del_object(v___x_5297_);
                    crate::leanh::lean_del_object(v___x_5292_);
                    v___x_5303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2);
                    v___x_5304_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5);
                    v___x_5305_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5305_, 0, v___x_5303_);
                    crate::leanh::lean_ctor_set(v___x_5305_, 1, v___x_5304_);
                    crate::leanh::lean_ctor_set(v___x_5305_, 2, v___x_5299_);
                    v___x_5306_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v___x_5305_,
                            v_snd_5295_,
                        );
                    return v___x_5306_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5299_);
                    v___x_5307_ = crate::leanh::lean_box(0);
                    if v_isShared_5298_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5297_, 0, v___x_5307_);
                        v___x_5309_ = v___x_5297_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5307_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 1, v_snd_5295_);
                        v___x_5309_ = v_reuseFailAlloc_5313_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5292_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
                    v___x_5311_ = v_reuseFailAlloc_5312_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5311_;
            }
            5 => {
                if v_isShared_5319_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5322_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5321_;
            }
            7 => {
                if v_isShared_5327_ == 0 {
                    v___x_5329_ = v___x_5326_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
                    v___x_5329_ = v_reuseFailAlloc_5330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(
    mut v_a_5332_: *mut crate::leanh::LeanObject,
    mut v_a_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_a_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5339_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(
        v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_,
    );
    crate::leanh::lean_dec(v_a_5337_);
    crate::leanh::lean_dec_ref(v_a_5336_);
    crate::leanh::lean_dec(v_a_5335_);
    crate::leanh::lean_dec_ref(v_a_5334_);
    crate::leanh::lean_dec_ref(v_a_5332_);
    return v_res_5339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(
    mut v_sz_5340_: usize,
    mut v_i_5341_: usize,
    mut v_bs_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_5340_, v_i_5341_, v_bs_5342_, v___y_5344_);
    return v___x_5350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(
    mut v_sz_5351_: *mut crate::leanh::LeanObject,
    mut v_i_5352_: *mut crate::leanh::LeanObject,
    mut v_bs_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5361_: usize = 0;
    let mut v_i_boxed_5362_: usize = 0;
    let mut v_res_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5361_ = crate::leanh::lean_unbox_usize(v_sz_5351_);
    crate::leanh::lean_dec(v_sz_5351_);
    v_i_boxed_5362_ = crate::leanh::lean_unbox_usize(v_i_5352_);
    crate::leanh::lean_dec(v_i_5352_);
    v_res_5363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(v_sz_boxed_5361_, v_i_boxed_5362_, v_bs_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
    crate::leanh::lean_dec(v___y_5359_);
    crate::leanh::lean_dec_ref(v___y_5358_);
    crate::leanh::lean_dec(v___y_5357_);
    crate::leanh::lean_dec_ref(v___y_5356_);
    crate::leanh::lean_dec_ref(v___y_5354_);
    return v_res_5363_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(
    mut v_x_5364_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5365_: u8 = 0;
    v___x_5365_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_5364_);
    return v___x_5365_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(
    mut v_x_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5367_: u8 = 0;
    let mut v_r_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5367_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(v_x_5366_);
    crate::leanh::lean_dec_ref(v_x_5366_);
    v_r_5368_ = crate::leanh::lean_box((v_res_5367_) as usize);
    return v_r_5368_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(
    mut v_00_u03b2_5369_: *mut crate::leanh::LeanObject,
    mut v_x_5370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5371_: u8 = 0;
    v___x_5371_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_5370_);
    return v___x_5371_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(
    mut v_00_u03b2_5372_: *mut crate::leanh::LeanObject,
    mut v_x_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5374_: u8 = 0;
    let mut v_r_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5374_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(
            v_00_u03b2_5372_,
            v_x_5373_,
        );
    crate::leanh::lean_dec_ref(v_x_5373_);
    v_r_5375_ = crate::leanh::lean_box((v_res_5374_) as usize);
    return v_r_5375_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(
    mut v_as_5380_: *mut crate::leanh::LeanObject,
    mut v_sz_5381_: usize,
    mut v_i_5382_: usize,
    mut v_b_5383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5392_: u8 = 0;
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: f64 = 0.0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5403_: u8 = 0;
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: usize = 0;
    let mut v___x_5417_: usize = 0;
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: u8 = 0;
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_isSharedCheck_5430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5385_ = lean_usize_dec_lt(v_i_5382_, v_sz_5381_);
                if v___x_5385_ == 0 {
                    v___x_5386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v_b_5383_);
                    return v___x_5386_;
                } else {
                    v_a_5387_ = lean_array_uget(v_as_5380_, v_i_5382_);
                    v_fst_5388_ = crate::leanh::lean_ctor_get(v_a_5387_, 0);
                    v_snd_5389_ = crate::leanh::lean_ctor_get(v_a_5387_, 1);
                    v_isSharedCheck_5430_ = (!crate::leanh::lean_is_exclusive(v_a_5387_)) as u8;
                    if v_isSharedCheck_5430_ == 0 {
                        v___x_5391_ = v_a_5387_;
                        v_isShared_5392_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5389_);
                        crate::leanh::lean_inc(v_fst_5388_);
                        crate::leanh::lean_dec(v_a_5387_);
                        v___x_5391_ = crate::leanh::lean_box(0);
                        v_isShared_5392_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5393_ =
                    l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                v___x_5394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1;
                v___x_5395_ = crate::leanh::lean_box(0);
                v___x_5396_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once), _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
                v___x_5397_ = l_Lean_Meta_Grind_ppGoals___closed__0;
                v___x_5398_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5394_);
                crate::leanh::lean_ctor_set(v___x_5398_, 1, v___x_5395_);
                crate::leanh::lean_ctor_set(v___x_5398_, 2, v___x_5397_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5398_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5396_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5398_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5396_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5398_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5385_,
                );
                v_num_5399_ = crate::leanh::lean_ctor_get(v_snd_5389_, 0);
                v_den_5400_ = crate::leanh::lean_ctor_get(v_snd_5389_, 1);
                v_isSharedCheck_5429_ = (!crate::leanh::lean_is_exclusive(v_snd_5389_)) as u8;
                if v_isSharedCheck_5429_ == 0 {
                    v___x_5402_ = v_snd_5389_;
                    v_isShared_5403_ = v_isSharedCheck_5429_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_den_5400_);
                    crate::leanh::lean_inc(v_num_5399_);
                    crate::leanh::lean_dec(v_snd_5389_);
                    v___x_5402_ = crate::leanh::lean_box(0);
                    v_isShared_5403_ = v_isSharedCheck_5429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5404_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_5388_);
                v___x_5405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
                if v_isShared_5403_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5402_, 7);
                    crate::leanh::lean_ctor_set(v___x_5402_, 1, v___x_5405_);
                    crate::leanh::lean_ctor_set(v___x_5402_, 0, v___x_5404_);
                    v___x_5407_ = v___x_5402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 1, v___x_5405_);
                    v___x_5407_ = v_reuseFailAlloc_5428_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5420_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5421_ = lean_nat_dec_eq(v_den_5400_, v___x_5420_);
                if v___x_5421_ == 0 {
                    v___x_5422_ = l_Int_repr(v_num_5399_);
                    crate::leanh::lean_dec(v_num_5399_);
                    v___x_5423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2;
                    v___x_5424_ = lean_string_append(v___x_5422_, v___x_5423_);
                    v___x_5425_ = l_Nat_reprFast(v_den_5400_);
                    v___x_5426_ = lean_string_append(v___x_5424_, v___x_5425_);
                    crate::leanh::lean_dec_ref(v___x_5425_);
                    v___y_5409_ = v___x_5426_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_den_5400_);
                    v___x_5427_ = l_Int_repr(v_num_5399_);
                    crate::leanh::lean_dec(v_num_5399_);
                    v___y_5409_ = v___x_5427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5410_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5410_, 0, v___y_5409_);
                v___x_5411_ = l_Lean_MessageData_ofFormat(v___x_5410_);
                if v_isShared_5392_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5391_, 7);
                    crate::leanh::lean_ctor_set(v___x_5391_, 1, v___x_5411_);
                    crate::leanh::lean_ctor_set(v___x_5391_, 0, v___x_5407_);
                    v___x_5413_ = v___x_5391_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5411_);
                    v___x_5413_ = v_reuseFailAlloc_5419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5414_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5398_);
                crate::leanh::lean_ctor_set(v___x_5414_, 1, v___x_5413_);
                crate::leanh::lean_ctor_set(v___x_5414_, 2, v___x_5393_);
                v___x_5415_ = lean_array_push(v_b_5383_, v___x_5414_);
                v___x_5416_ = 1usize;
                v___x_5417_ = lean_usize_add(v_i_5382_, v___x_5416_);
                v_i_5382_ = v___x_5417_;
                v_b_5383_ = v___x_5415_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(
    mut v_as_5431_: *mut crate::leanh::LeanObject,
    mut v_sz_5432_: *mut crate::leanh::LeanObject,
    mut v_i_5433_: *mut crate::leanh::LeanObject,
    mut v_b_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5436_: usize = 0;
    let mut v_i_boxed_5437_: usize = 0;
    let mut v_res_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5436_ = crate::leanh::lean_unbox_usize(v_sz_5432_);
    crate::leanh::lean_dec(v_sz_5432_);
    v_i_boxed_5437_ = crate::leanh::lean_unbox_usize(v_i_5433_);
    crate::leanh::lean_dec(v_i_5433_);
    v_res_5438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_5431_, v_sz_boxed_5436_, v_i_boxed_5437_, v_b_5434_);
    crate::leanh::lean_dec_ref(v_as_5431_);
    return v_res_5438_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: u8 = 0;
    let mut v___x_5444_: f64 = 0.0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5442_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_5443_ = 1;
    v___x_5444_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_5445_ = crate::leanh::lean_box(0);
    v___x_5446_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1;
    v___x_5447_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_5447_, 0, v___x_5446_);
    crate::leanh::lean_ctor_set(v___x_5447_, 1, v___x_5445_);
    crate::leanh::lean_ctor_set(v___x_5447_, 2, v___x_5442_);
    crate::leanh::lean_ctor_set_float(
        v___x_5447_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5444_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_5447_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_5444_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5447_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_5443_,
    );
    return v___x_5447_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5451_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4;
    v___x_5452_ = l_Lean_MessageData_ofFormat(v___x_5451_);
    return v___x_5452_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(
    mut v_goal_5453_: *mut crate::leanh::LeanObject,
    mut v_a_5454_: *mut crate::leanh::LeanObject,
    mut v_a_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v_varMap_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5471_: u8 = 0;
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: u8 = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5476_: usize = 0;
    let mut v___x_5477_: usize = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5482_: u8 = 0;
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5490_: u8 = 0;
    let mut v_a_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5498_: u8 = 0;
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v_a_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v_a_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5520_: u8 = 0;
    let mut v_ref_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5459_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                v___x_5460_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_5459_, v_goal_5453_);
                if crate::leanh::lean_obj_tag(v___x_5460_) == 0 {
                    v_a_5461_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                    v_isSharedCheck_5516_ = (!crate::leanh::lean_is_exclusive(v___x_5460_)) as u8;
                    if v_isSharedCheck_5516_ == 0 {
                        v___x_5463_ = v___x_5460_;
                        v_isShared_5464_ = v_isSharedCheck_5516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5461_);
                        crate::leanh::lean_dec(v___x_5460_);
                        v___x_5463_ = crate::leanh::lean_box(0);
                        v_isShared_5464_ = v_isSharedCheck_5516_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5517_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                    v_isSharedCheck_5529_ = (!crate::leanh::lean_is_exclusive(v___x_5460_)) as u8;
                    if v_isSharedCheck_5529_ == 0 {
                        v___x_5519_ = v___x_5460_;
                        v_isShared_5520_ = v_isSharedCheck_5529_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5517_);
                        crate::leanh::lean_dec(v___x_5460_);
                        v___x_5519_ = crate::leanh::lean_box(0);
                        v_isShared_5520_ = v_isSharedCheck_5529_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_varMap_5465_ = crate::leanh::lean_ctor_get(v_a_5461_, 1);
                crate::leanh::lean_inc_ref(v_varMap_5465_);
                crate::leanh::lean_dec(v_a_5461_);
                v___x_5466_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_varMap_5465_);
                crate::leanh::lean_dec_ref(v_varMap_5465_);
                if v___x_5466_ == 0 {
                    crate::leanh::lean_del_object(v___x_5463_);
                    v___x_5467_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(
                        v_goal_5453_,
                        v_a_5454_,
                        v_a_5455_,
                        v_a_5456_,
                        v_a_5457_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5467_) == 0 {
                        v_a_5468_ = crate::leanh::lean_ctor_get(v___x_5467_, 0);
                        v_isSharedCheck_5503_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5467_)) as u8;
                        if v_isSharedCheck_5503_ == 0 {
                            v___x_5470_ = v___x_5467_;
                            v_isShared_5471_ = v_isSharedCheck_5503_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5468_);
                            crate::leanh::lean_dec(v___x_5467_);
                            v___x_5470_ = crate::leanh::lean_box(0);
                            v_isShared_5471_ = v_isSharedCheck_5503_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5504_ = crate::leanh::lean_ctor_get(v___x_5467_, 0);
                        v_isSharedCheck_5511_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5467_)) as u8;
                        if v_isSharedCheck_5511_ == 0 {
                            v___x_5506_ = v___x_5467_;
                            v_isShared_5507_ = v_isSharedCheck_5511_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5504_);
                            crate::leanh::lean_dec(v___x_5467_);
                            v___x_5506_ = crate::leanh::lean_box(0);
                            v_isShared_5507_ = v_isSharedCheck_5511_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_5512_ = crate::leanh::lean_box(0);
                    if v_isShared_5464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5463_, 0, v___x_5512_);
                        v___x_5514_ = v___x_5463_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5512_);
                        v___x_5514_ = v_reuseFailAlloc_5515_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5472_ = lean_array_get_size(v_a_5468_);
                v___x_5473_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5474_ = lean_nat_dec_eq(v___x_5472_, v___x_5473_);
                if v___x_5474_ == 0 {
                    crate::leanh::lean_del_object(v___x_5470_);
                    v___x_5475_ =
                        l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                    v_sz_5476_ = lean_array_size(v_a_5468_);
                    v___x_5477_ = 0usize;
                    v___x_5478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_a_5468_, v_sz_5476_, v___x_5477_, v___x_5475_);
                    crate::leanh::lean_dec(v_a_5468_);
                    if crate::leanh::lean_obj_tag(v___x_5478_) == 0 {
                        v_a_5479_ = crate::leanh::lean_ctor_get(v___x_5478_, 0);
                        v_isSharedCheck_5490_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5478_)) as u8;
                        if v_isSharedCheck_5490_ == 0 {
                            v___x_5481_ = v___x_5478_;
                            v_isShared_5482_ = v_isSharedCheck_5490_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5479_);
                            crate::leanh::lean_dec(v___x_5478_);
                            v___x_5481_ = crate::leanh::lean_box(0);
                            v_isShared_5482_ = v_isSharedCheck_5490_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5491_ = crate::leanh::lean_ctor_get(v___x_5478_, 0);
                        v_isSharedCheck_5498_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5478_)) as u8;
                        if v_isSharedCheck_5498_ == 0 {
                            v___x_5493_ = v___x_5478_;
                            v_isShared_5494_ = v_isSharedCheck_5498_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5491_);
                            crate::leanh::lean_dec(v___x_5478_);
                            v___x_5493_ = crate::leanh::lean_box(0);
                            v_isShared_5494_ = v_isSharedCheck_5498_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5468_);
                    v___x_5499_ = crate::leanh::lean_box(0);
                    if v_isShared_5471_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5470_, 0, v___x_5499_);
                        v___x_5501_ = v___x_5470_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5499_);
                        v___x_5501_ = v_reuseFailAlloc_5502_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5483_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2,
                );
                v___x_5484_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5,
                );
                v___x_5485_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5483_);
                crate::leanh::lean_ctor_set(v___x_5485_, 1, v___x_5484_);
                crate::leanh::lean_ctor_set(v___x_5485_, 2, v_a_5479_);
                v___x_5486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5486_, 0, v___x_5485_);
                if v_isShared_5482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5481_, 0, v___x_5486_);
                    v___x_5488_ = v___x_5481_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5486_);
                    v___x_5488_ = v_reuseFailAlloc_5489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5488_;
            }
            5 => {
                if v_isShared_5494_ == 0 {
                    v___x_5496_ = v___x_5493_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
                    v___x_5496_ = v_reuseFailAlloc_5497_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5496_;
            }
            7 => {
                return v___x_5501_;
            }
            8 => {
                if v_isShared_5507_ == 0 {
                    v___x_5509_ = v___x_5506_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
                    v___x_5509_ = v_reuseFailAlloc_5510_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5509_;
            }
            10 => {
                return v___x_5514_;
            }
            11 => {
                v_ref_5521_ = crate::leanh::lean_ctor_get(v_a_5456_, 5);
                v___x_5522_ = lean_io_error_to_string(v_a_5517_);
                v___x_5523_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5523_, 0, v___x_5522_);
                v___x_5524_ = l_Lean_MessageData_ofFormat(v___x_5523_);
                crate::leanh::lean_inc(v_ref_5521_);
                v___x_5525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5525_, 0, v_ref_5521_);
                crate::leanh::lean_ctor_set(v___x_5525_, 1, v___x_5524_);
                if v_isShared_5520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5519_, 0, v___x_5525_);
                    v___x_5527_ = v___x_5519_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
                    v___x_5527_ = v_reuseFailAlloc_5528_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(
    mut v_goal_5530_: *mut crate::leanh::LeanObject,
    mut v_a_5531_: *mut crate::leanh::LeanObject,
    mut v_a_5532_: *mut crate::leanh::LeanObject,
    mut v_a_5533_: *mut crate::leanh::LeanObject,
    mut v_a_5534_: *mut crate::leanh::LeanObject,
    mut v_a_5535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5536_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(
        v_goal_5530_,
        v_a_5531_,
        v_a_5532_,
        v_a_5533_,
        v_a_5534_,
    );
    crate::leanh::lean_dec(v_a_5534_);
    crate::leanh::lean_dec_ref(v_a_5533_);
    crate::leanh::lean_dec(v_a_5532_);
    crate::leanh::lean_dec_ref(v_a_5531_);
    crate::leanh::lean_dec_ref(v_goal_5530_);
    return v_res_5536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(
    mut v_as_5537_: *mut crate::leanh::LeanObject,
    mut v_sz_5538_: usize,
    mut v_i_5539_: usize,
    mut v_b_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_5537_, v_sz_5538_, v_i_5539_, v_b_5540_);
    return v___x_5546_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(
    mut v_as_5547_: *mut crate::leanh::LeanObject,
    mut v_sz_5548_: *mut crate::leanh::LeanObject,
    mut v_i_5549_: *mut crate::leanh::LeanObject,
    mut v_b_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5556_: usize = 0;
    let mut v_i_boxed_5557_: usize = 0;
    let mut v_res_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5556_ = crate::leanh::lean_unbox_usize(v_sz_5548_);
    crate::leanh::lean_dec(v_sz_5548_);
    v_i_boxed_5557_ = crate::leanh::lean_unbox_usize(v_i_5549_);
    crate::leanh::lean_dec(v_i_5549_);
    v_res_5558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(v_as_5547_, v_sz_boxed_5556_, v_i_boxed_5557_, v_b_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
    crate::leanh::lean_dec(v___y_5554_);
    crate::leanh::lean_dec_ref(v___y_5553_);
    crate::leanh::lean_dec(v___y_5552_);
    crate::leanh::lean_dec_ref(v___y_5551_);
    crate::leanh::lean_dec_ref(v_as_5547_);
    return v_res_5558_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v_val_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_a_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5566_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(
                    v_a_5559_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_,
                );
                if crate::leanh::lean_obj_tag(v___x_5566_) == 0 {
                    v_a_5567_ = crate::leanh::lean_ctor_get(v___x_5566_, 0);
                    v_isSharedCheck_5578_ = (!crate::leanh::lean_is_exclusive(v___x_5566_)) as u8;
                    if v_isSharedCheck_5578_ == 0 {
                        v___x_5569_ = v___x_5566_;
                        v_isShared_5570_ = v_isSharedCheck_5578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5567_);
                        crate::leanh::lean_dec(v___x_5566_);
                        v___x_5569_ = crate::leanh::lean_box(0);
                        v_isShared_5570_ = v_isSharedCheck_5578_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5560_);
                    v_a_5579_ = crate::leanh::lean_ctor_get(v___x_5566_, 0);
                    v_isSharedCheck_5586_ = (!crate::leanh::lean_is_exclusive(v___x_5566_)) as u8;
                    if v_isSharedCheck_5586_ == 0 {
                        v___x_5581_ = v___x_5566_;
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5579_);
                        crate::leanh::lean_dec(v___x_5566_);
                        v___x_5581_ = crate::leanh::lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5567_) == 1 {
                    crate::leanh::lean_del_object(v___x_5569_);
                    v_val_5571_ = crate::leanh::lean_ctor_get(v_a_5567_, 0);
                    crate::leanh::lean_inc(v_val_5571_);
                    crate::leanh::lean_dec_ref_known(v_a_5567_, 1);
                    v___x_5572_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5571_,
                            v_a_5560_,
                        );
                    return v___x_5572_;
                } else {
                    crate::leanh::lean_dec(v_a_5567_);
                    v___x_5573_ = crate::leanh::lean_box(0);
                    v___x_5574_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5574_, 0, v___x_5573_);
                    crate::leanh::lean_ctor_set(v___x_5574_, 1, v_a_5560_);
                    if v_isShared_5570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5569_, 0, v___x_5574_);
                        v___x_5576_ = v___x_5569_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v___x_5574_);
                        v___x_5576_ = v_reuseFailAlloc_5577_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5576_;
            }
            3 => {
                if v_isShared_5582_ == 0 {
                    v___x_5584_ = v___x_5581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(
    mut v_a_5587_: *mut crate::leanh::LeanObject,
    mut v_a_5588_: *mut crate::leanh::LeanObject,
    mut v_a_5589_: *mut crate::leanh::LeanObject,
    mut v_a_5590_: *mut crate::leanh::LeanObject,
    mut v_a_5591_: *mut crate::leanh::LeanObject,
    mut v_a_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5594_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(
        v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_,
    );
    crate::leanh::lean_dec(v_a_5592_);
    crate::leanh::lean_dec_ref(v_a_5591_);
    crate::leanh::lean_dec(v_a_5590_);
    crate::leanh::lean_dec_ref(v_a_5589_);
    crate::leanh::lean_dec_ref(v_a_5587_);
    return v_res_5594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
    mut v_a_5598_: *mut crate::leanh::LeanObject,
    mut v_a_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v_val_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v_a_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5618_: u8 = 0;
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5602_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(
                    v_a_5595_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_,
                );
                if crate::leanh::lean_obj_tag(v___x_5602_) == 0 {
                    v_a_5603_ = crate::leanh::lean_ctor_get(v___x_5602_, 0);
                    v_isSharedCheck_5614_ = (!crate::leanh::lean_is_exclusive(v___x_5602_)) as u8;
                    if v_isSharedCheck_5614_ == 0 {
                        v___x_5605_ = v___x_5602_;
                        v_isShared_5606_ = v_isSharedCheck_5614_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5603_);
                        crate::leanh::lean_dec(v___x_5602_);
                        v___x_5605_ = crate::leanh::lean_box(0);
                        v_isShared_5606_ = v_isSharedCheck_5614_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5596_);
                    v_a_5615_ = crate::leanh::lean_ctor_get(v___x_5602_, 0);
                    v_isSharedCheck_5622_ = (!crate::leanh::lean_is_exclusive(v___x_5602_)) as u8;
                    if v_isSharedCheck_5622_ == 0 {
                        v___x_5617_ = v___x_5602_;
                        v_isShared_5618_ = v_isSharedCheck_5622_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5615_);
                        crate::leanh::lean_dec(v___x_5602_);
                        v___x_5617_ = crate::leanh::lean_box(0);
                        v_isShared_5618_ = v_isSharedCheck_5622_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5603_) == 1 {
                    crate::leanh::lean_del_object(v___x_5605_);
                    v_val_5607_ = crate::leanh::lean_ctor_get(v_a_5603_, 0);
                    crate::leanh::lean_inc(v_val_5607_);
                    crate::leanh::lean_dec_ref_known(v_a_5603_, 1);
                    v___x_5608_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5607_,
                            v_a_5596_,
                        );
                    return v___x_5608_;
                } else {
                    crate::leanh::lean_dec(v_a_5603_);
                    v___x_5609_ = crate::leanh::lean_box(0);
                    v___x_5610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5610_, 0, v___x_5609_);
                    crate::leanh::lean_ctor_set(v___x_5610_, 1, v_a_5596_);
                    if v_isShared_5606_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5605_, 0, v___x_5610_);
                        v___x_5612_ = v___x_5605_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
                        v___x_5612_ = v_reuseFailAlloc_5613_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5612_;
            }
            3 => {
                if v_isShared_5618_ == 0 {
                    v___x_5620_ = v___x_5617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
                    v___x_5620_ = v_reuseFailAlloc_5621_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(
    mut v_a_5623_: *mut crate::leanh::LeanObject,
    mut v_a_5624_: *mut crate::leanh::LeanObject,
    mut v_a_5625_: *mut crate::leanh::LeanObject,
    mut v_a_5626_: *mut crate::leanh::LeanObject,
    mut v_a_5627_: *mut crate::leanh::LeanObject,
    mut v_a_5628_: *mut crate::leanh::LeanObject,
    mut v_a_5629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5630_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(
        v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_,
    );
    crate::leanh::lean_dec(v_a_5628_);
    crate::leanh::lean_dec_ref(v_a_5627_);
    crate::leanh::lean_dec(v_a_5626_);
    crate::leanh::lean_dec_ref(v_a_5625_);
    crate::leanh::lean_dec_ref(v_a_5623_);
    return v_res_5630_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(
    mut v_a_5631_: *mut crate::leanh::LeanObject,
    mut v_a_5632_: *mut crate::leanh::LeanObject,
    mut v_a_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v_val_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_a_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5638_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(
                    v_a_5631_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_,
                );
                if crate::leanh::lean_obj_tag(v___x_5638_) == 0 {
                    v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                    v_isSharedCheck_5650_ = (!crate::leanh::lean_is_exclusive(v___x_5638_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5641_ = v___x_5638_;
                        v_isShared_5642_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5639_);
                        crate::leanh::lean_dec(v___x_5638_);
                        v___x_5641_ = crate::leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5632_);
                    v_a_5651_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                    v_isSharedCheck_5658_ = (!crate::leanh::lean_is_exclusive(v___x_5638_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5638_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5651_);
                        crate::leanh::lean_dec(v___x_5638_);
                        v___x_5653_ = crate::leanh::lean_box(0);
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5639_) == 1 {
                    crate::leanh::lean_del_object(v___x_5641_);
                    v_val_5643_ = crate::leanh::lean_ctor_get(v_a_5639_, 0);
                    crate::leanh::lean_inc(v_val_5643_);
                    crate::leanh::lean_dec_ref_known(v_a_5639_, 1);
                    v___x_5644_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5643_,
                            v_a_5632_,
                        );
                    return v___x_5644_;
                } else {
                    crate::leanh::lean_dec(v_a_5639_);
                    v___x_5645_ = crate::leanh::lean_box(0);
                    v___x_5646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5646_, 0, v___x_5645_);
                    crate::leanh::lean_ctor_set(v___x_5646_, 1, v_a_5632_);
                    if v_isShared_5642_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5641_, 0, v___x_5646_);
                        v___x_5648_ = v___x_5641_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
                        v___x_5648_ = v_reuseFailAlloc_5649_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5648_;
            }
            3 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(
    mut v_a_5659_: *mut crate::leanh::LeanObject,
    mut v_a_5660_: *mut crate::leanh::LeanObject,
    mut v_a_5661_: *mut crate::leanh::LeanObject,
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v_a_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
    mut v_a_5665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5666_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(
        v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_,
    );
    crate::leanh::lean_dec(v_a_5664_);
    crate::leanh::lean_dec_ref(v_a_5663_);
    crate::leanh::lean_dec(v_a_5662_);
    crate::leanh::lean_dec_ref(v_a_5661_);
    crate::leanh::lean_dec_ref(v_a_5659_);
    return v_res_5666_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(
    mut v_a_5667_: *mut crate::leanh::LeanObject,
    mut v_a_5668_: *mut crate::leanh::LeanObject,
    mut v_a_5669_: *mut crate::leanh::LeanObject,
    mut v_a_5670_: *mut crate::leanh::LeanObject,
    mut v_a_5671_: *mut crate::leanh::LeanObject,
    mut v_a_5672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5678_: u8 = 0;
    let mut v_val_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut v_a_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5690_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5674_ = l_Lean_Meta_Grind_AC_pp_x3f(
                    v_a_5667_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_,
                );
                if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
                    v_a_5675_ = crate::leanh::lean_ctor_get(v___x_5674_, 0);
                    v_isSharedCheck_5686_ = (!crate::leanh::lean_is_exclusive(v___x_5674_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5677_ = v___x_5674_;
                        v_isShared_5678_ = v_isSharedCheck_5686_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5675_);
                        crate::leanh::lean_dec(v___x_5674_);
                        v___x_5677_ = crate::leanh::lean_box(0);
                        v_isShared_5678_ = v_isSharedCheck_5686_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5668_);
                    v_a_5687_ = crate::leanh::lean_ctor_get(v___x_5674_, 0);
                    v_isSharedCheck_5694_ = (!crate::leanh::lean_is_exclusive(v___x_5674_)) as u8;
                    if v_isSharedCheck_5694_ == 0 {
                        v___x_5689_ = v___x_5674_;
                        v_isShared_5690_ = v_isSharedCheck_5694_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5687_);
                        crate::leanh::lean_dec(v___x_5674_);
                        v___x_5689_ = crate::leanh::lean_box(0);
                        v_isShared_5690_ = v_isSharedCheck_5694_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5675_) == 1 {
                    crate::leanh::lean_del_object(v___x_5677_);
                    v_val_5679_ = crate::leanh::lean_ctor_get(v_a_5675_, 0);
                    crate::leanh::lean_inc(v_val_5679_);
                    crate::leanh::lean_dec_ref_known(v_a_5675_, 1);
                    v___x_5680_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v_val_5679_,
                            v_a_5668_,
                        );
                    return v___x_5680_;
                } else {
                    crate::leanh::lean_dec(v_a_5675_);
                    v___x_5681_ = crate::leanh::lean_box(0);
                    v___x_5682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5682_, 0, v___x_5681_);
                    crate::leanh::lean_ctor_set(v___x_5682_, 1, v_a_5668_);
                    if v_isShared_5678_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5677_, 0, v___x_5682_);
                        v___x_5684_ = v___x_5677_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5685_, 0, v___x_5682_);
                        v___x_5684_ = v_reuseFailAlloc_5685_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5684_;
            }
            3 => {
                if v_isShared_5690_ == 0 {
                    v___x_5692_ = v___x_5689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_a_5687_);
                    v___x_5692_ = v_reuseFailAlloc_5693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5702_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(
        v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_,
    );
    crate::leanh::lean_dec(v_a_5700_);
    crate::leanh::lean_dec_ref(v_a_5699_);
    crate::leanh::lean_dec(v_a_5698_);
    crate::leanh::lean_dec_ref(v_a_5697_);
    crate::leanh::lean_dec_ref(v_a_5695_);
    return v_res_5702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(
    mut v_a_5703_: *mut crate::leanh::LeanObject,
    mut v_as_5704_: *mut crate::leanh::LeanObject,
    mut v_i_5705_: usize,
    mut v_stop_5706_: usize,
    mut v_b_5707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: usize = 0;
    let mut v___x_5711_: usize = 0;
    let mut v___x_5713_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generation_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5713_ = lean_usize_dec_eq(v_i_5705_, v_stop_5706_);
                if v___x_5713_ == 0 {
                    v___x_5714_ = lean_array_uget_borrowed(v_as_5704_, v_i_5705_);
                    v___x_5715_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_a_5703_, v___x_5714_);
                    if crate::leanh::lean_obj_tag(v___x_5715_) == 1 {
                        v_val_5716_ = crate::leanh::lean_ctor_get(v___x_5715_, 0);
                        crate::leanh::lean_inc(v_val_5716_);
                        crate::leanh::lean_dec_ref_known(v___x_5715_, 1);
                        v_generation_5717_ = crate::leanh::lean_ctor_get(v_val_5716_, 8);
                        crate::leanh::lean_inc(v_generation_5717_);
                        crate::leanh::lean_dec(v_val_5716_);
                        v___x_5718_ = lean_nat_dec_le(v_b_5707_, v_generation_5717_);
                        if v___x_5718_ == 0 {
                            crate::leanh::lean_dec(v_generation_5717_);
                            v___y_5709_ = v_b_5707_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_5707_);
                            v___y_5709_ = v_generation_5717_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5715_);
                        v___y_5709_ = v_b_5707_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5707_;
                }
            }
            1 => {
                v___x_5710_ = 1usize;
                v___x_5711_ = lean_usize_add(v_i_5705_, v___x_5710_);
                v_i_5705_ = v___x_5711_;
                v_b_5707_ = v___y_5709_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(
    mut v_a_5719_: *mut crate::leanh::LeanObject,
    mut v_as_5720_: *mut crate::leanh::LeanObject,
    mut v_i_5721_: *mut crate::leanh::LeanObject,
    mut v_stop_5722_: *mut crate::leanh::LeanObject,
    mut v_b_5723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5724_: usize = 0;
    let mut v_stop_boxed_5725_: usize = 0;
    let mut v_res_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5724_ = crate::leanh::lean_unbox_usize(v_i_5721_);
    crate::leanh::lean_dec(v_i_5721_);
    v_stop_boxed_5725_ = crate::leanh::lean_unbox_usize(v_stop_5722_);
    crate::leanh::lean_dec(v_stop_5722_);
    v_res_5726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5719_, v_as_5720_, v_i_boxed_5724_, v_stop_boxed_5725_, v_b_5723_);
    crate::leanh::lean_dec_ref(v_as_5720_);
    crate::leanh::lean_dec_ref(v_a_5719_);
    return v_res_5726_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(
    mut v_a_5727_: *mut crate::leanh::LeanObject,
    mut v_x_5728_: *mut crate::leanh::LeanObject,
    mut v_x_5729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5728_) == 0 {
        let mut v_cs_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5733_: u8 = 0;
        v_cs_5730_ = crate::leanh::lean_ctor_get(v_x_5728_, 0);
        v___x_5731_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5732_ = lean_array_get_size(v_cs_5730_);
        v___x_5733_ = lean_nat_dec_lt(v___x_5731_, v___x_5732_);
        if v___x_5733_ == 0 {
            return v_x_5729_;
        } else {
            let mut v___x_5734_: u8 = 0;
            v___x_5734_ = lean_nat_dec_le(v___x_5732_, v___x_5732_);
            if v___x_5734_ == 0 {
                if v___x_5733_ == 0 {
                    return v_x_5729_;
                } else {
                    let mut v___x_5735_: usize = 0;
                    let mut v___x_5736_: usize = 0;
                    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5735_ = 0usize;
                    v___x_5736_ = lean_usize_of_nat(v___x_5732_);
                    v___x_5737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_5727_, v_cs_5730_, v___x_5735_, v___x_5736_, v_x_5729_);
                    return v___x_5737_;
                }
            } else {
                let mut v___x_5738_: usize = 0;
                let mut v___x_5739_: usize = 0;
                let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5738_ = 0usize;
                v___x_5739_ = lean_usize_of_nat(v___x_5732_);
                v___x_5740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_5727_, v_cs_5730_, v___x_5738_, v___x_5739_, v_x_5729_);
                return v___x_5740_;
            }
        }
    } else {
        let mut v_vs_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5744_: u8 = 0;
        v_vs_5741_ = crate::leanh::lean_ctor_get(v_x_5728_, 0);
        v___x_5742_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5743_ = lean_array_get_size(v_vs_5741_);
        v___x_5744_ = lean_nat_dec_lt(v___x_5742_, v___x_5743_);
        if v___x_5744_ == 0 {
            return v_x_5729_;
        } else {
            let mut v___x_5745_: u8 = 0;
            v___x_5745_ = lean_nat_dec_le(v___x_5743_, v___x_5743_);
            if v___x_5745_ == 0 {
                if v___x_5744_ == 0 {
                    return v_x_5729_;
                } else {
                    let mut v___x_5746_: usize = 0;
                    let mut v___x_5747_: usize = 0;
                    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5746_ = 0usize;
                    v___x_5747_ = lean_usize_of_nat(v___x_5743_);
                    v___x_5748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5727_, v_vs_5741_, v___x_5746_, v___x_5747_, v_x_5729_);
                    return v___x_5748_;
                }
            } else {
                let mut v___x_5749_: usize = 0;
                let mut v___x_5750_: usize = 0;
                let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5749_ = 0usize;
                v___x_5750_ = lean_usize_of_nat(v___x_5743_);
                v___x_5751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5727_, v_vs_5741_, v___x_5749_, v___x_5750_, v_x_5729_);
                return v___x_5751_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(
    mut v_a_5752_: *mut crate::leanh::LeanObject,
    mut v_as_5753_: *mut crate::leanh::LeanObject,
    mut v_i_5754_: usize,
    mut v_stop_5755_: usize,
    mut v_b_5756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5757_: u8 = 0;
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: usize = 0;
    let mut v___x_5761_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5757_ = lean_usize_dec_eq(v_i_5754_, v_stop_5755_);
                if v___x_5757_ == 0 {
                    v___x_5758_ = lean_array_uget_borrowed(v_as_5753_, v_i_5754_);
                    v___x_5759_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_5752_, v___x_5758_, v_b_5756_);
                    v___x_5760_ = 1usize;
                    v___x_5761_ = lean_usize_add(v_i_5754_, v___x_5760_);
                    v_i_5754_ = v___x_5761_;
                    v_b_5756_ = v___x_5759_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5756_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1___boxed(
    mut v_a_5763_: *mut crate::leanh::LeanObject,
    mut v_as_5764_: *mut crate::leanh::LeanObject,
    mut v_i_5765_: *mut crate::leanh::LeanObject,
    mut v_stop_5766_: *mut crate::leanh::LeanObject,
    mut v_b_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5768_: usize = 0;
    let mut v_stop_boxed_5769_: usize = 0;
    let mut v_res_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5768_ = crate::leanh::lean_unbox_usize(v_i_5765_);
    crate::leanh::lean_dec(v_i_5765_);
    v_stop_boxed_5769_ = crate::leanh::lean_unbox_usize(v_stop_5766_);
    crate::leanh::lean_dec(v_stop_5766_);
    v_res_5770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_5763_, v_as_5764_, v_i_boxed_5768_, v_stop_boxed_5769_, v_b_5767_);
    crate::leanh::lean_dec_ref(v_as_5764_);
    crate::leanh::lean_dec_ref(v_a_5763_);
    return v_res_5770_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2___boxed(
    mut v_a_5771_: *mut crate::leanh::LeanObject,
    mut v_x_5772_: *mut crate::leanh::LeanObject,
    mut v_x_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5774_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_5771_, v_x_5772_, v_x_5773_);
    crate::leanh::lean_dec_ref(v_x_5772_);
    crate::leanh::lean_dec_ref(v_a_5771_);
    return v_res_5774_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5775_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_5775_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_x_5777_: *mut crate::leanh::LeanObject,
    mut v_x_5778_: usize,
    mut v_x_5779_: usize,
    mut v_x_5780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5777_) == 0 {
        let mut v_cs_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5783_: usize = 0;
        let mut v_j_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5786_: usize = 0;
        let mut v___x_5787_: usize = 0;
        let mut v___x_5788_: usize = 0;
        let mut v___x_5789_: usize = 0;
        let mut v___x_5790_: usize = 0;
        let mut v___x_5791_: usize = 0;
        let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5796_: u8 = 0;
        v_cs_5781_ = crate::leanh::lean_ctor_get(v_x_5777_, 0);
        v___x_5782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0);
        v___x_5783_ = lean_usize_shift_right(v_x_5778_, v_x_5779_);
        v_j_5784_ = lean_usize_to_nat(v___x_5783_);
        v___x_5785_ = lean_array_get_borrowed(v___x_5782_, v_cs_5781_, v_j_5784_);
        v___x_5786_ = 1usize;
        v___x_5787_ = lean_usize_shift_left(v___x_5786_, v_x_5779_);
        v___x_5788_ = lean_usize_sub(v___x_5787_, v___x_5786_);
        v___x_5789_ = lean_usize_land(v_x_5778_, v___x_5788_);
        v___x_5790_ = 5usize;
        v___x_5791_ = lean_usize_sub(v_x_5779_, v___x_5790_);
        v___x_5792_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_5776_, v___x_5785_, v___x_5789_, v___x_5791_, v_x_5780_);
        v___x_5793_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5794_ = lean_nat_add(v_j_5784_, v___x_5793_);
        crate::leanh::lean_dec(v_j_5784_);
        v___x_5795_ = lean_array_get_size(v_cs_5781_);
        v___x_5796_ = lean_nat_dec_lt(v___x_5794_, v___x_5795_);
        if v___x_5796_ == 0 {
            crate::leanh::lean_dec(v___x_5794_);
            return v___x_5792_;
        } else {
            let mut v___x_5797_: u8 = 0;
            v___x_5797_ = lean_nat_dec_le(v___x_5795_, v___x_5795_);
            if v___x_5797_ == 0 {
                if v___x_5796_ == 0 {
                    crate::leanh::lean_dec(v___x_5794_);
                    return v___x_5792_;
                } else {
                    let mut v___x_5798_: usize = 0;
                    let mut v___x_5799_: usize = 0;
                    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5798_ = lean_usize_of_nat(v___x_5794_);
                    crate::leanh::lean_dec(v___x_5794_);
                    v___x_5799_ = lean_usize_of_nat(v___x_5795_);
                    v___x_5800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_5776_, v_cs_5781_, v___x_5798_, v___x_5799_, v___x_5792_);
                    return v___x_5800_;
                }
            } else {
                let mut v___x_5801_: usize = 0;
                let mut v___x_5802_: usize = 0;
                let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5801_ = lean_usize_of_nat(v___x_5794_);
                crate::leanh::lean_dec(v___x_5794_);
                v___x_5802_ = lean_usize_of_nat(v___x_5795_);
                v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_5776_, v_cs_5781_, v___x_5801_, v___x_5802_, v___x_5792_);
                return v___x_5803_;
            }
        }
    } else {
        let mut v_vs_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5807_: u8 = 0;
        v_vs_5804_ = crate::leanh::lean_ctor_get(v_x_5777_, 0);
        v___x_5805_ = lean_usize_to_nat(v_x_5778_);
        v___x_5806_ = lean_array_get_size(v_vs_5804_);
        v___x_5807_ = lean_nat_dec_lt(v___x_5805_, v___x_5806_);
        if v___x_5807_ == 0 {
            crate::leanh::lean_dec(v___x_5805_);
            return v_x_5780_;
        } else {
            let mut v___x_5808_: u8 = 0;
            v___x_5808_ = lean_nat_dec_le(v___x_5806_, v___x_5806_);
            if v___x_5808_ == 0 {
                if v___x_5807_ == 0 {
                    crate::leanh::lean_dec(v___x_5805_);
                    return v_x_5780_;
                } else {
                    let mut v___x_5809_: usize = 0;
                    let mut v___x_5810_: usize = 0;
                    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5809_ = lean_usize_of_nat(v___x_5805_);
                    crate::leanh::lean_dec(v___x_5805_);
                    v___x_5810_ = lean_usize_of_nat(v___x_5806_);
                    v___x_5811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5776_, v_vs_5804_, v___x_5809_, v___x_5810_, v_x_5780_);
                    return v___x_5811_;
                }
            } else {
                let mut v___x_5812_: usize = 0;
                let mut v___x_5813_: usize = 0;
                let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5812_ = lean_usize_of_nat(v___x_5805_);
                crate::leanh::lean_dec(v___x_5805_);
                v___x_5813_ = lean_usize_of_nat(v___x_5806_);
                v___x_5814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5776_, v_vs_5804_, v___x_5812_, v___x_5813_, v_x_5780_);
                return v___x_5814_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(
    mut v_a_5815_: *mut crate::leanh::LeanObject,
    mut v_x_5816_: *mut crate::leanh::LeanObject,
    mut v_x_5817_: *mut crate::leanh::LeanObject,
    mut v_x_5818_: *mut crate::leanh::LeanObject,
    mut v_x_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5395__boxed_5820_: usize = 0;
    let mut v_x_5396__boxed_5821_: usize = 0;
    let mut v_res_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5395__boxed_5820_ = crate::leanh::lean_unbox_usize(v_x_5817_);
    crate::leanh::lean_dec(v_x_5817_);
    v_x_5396__boxed_5821_ = crate::leanh::lean_unbox_usize(v_x_5818_);
    crate::leanh::lean_dec(v_x_5818_);
    v_res_5822_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_5815_, v_x_5816_, v_x_5395__boxed_5820_, v_x_5396__boxed_5821_, v_x_5819_);
    crate::leanh::lean_dec_ref(v_x_5816_);
    crate::leanh::lean_dec_ref(v_a_5815_);
    return v_res_5822_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(
    mut v_a_5823_: *mut crate::leanh::LeanObject,
    mut v_t_5824_: *mut crate::leanh::LeanObject,
    mut v_init_5825_: *mut crate::leanh::LeanObject,
    mut v_start_5826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    v___x_5827_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5828_ = lean_nat_dec_eq(v_start_5826_, v___x_5827_);
    if v___x_5828_ == 0 {
        let mut v_root_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_5831_: usize = 0;
        let mut v_tailOff_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5833_: u8 = 0;
        v_root_5829_ = crate::leanh::lean_ctor_get(v_t_5824_, 0);
        v_tail_5830_ = crate::leanh::lean_ctor_get(v_t_5824_, 1);
        v_shift_5831_ = crate::leanh::lean_ctor_get_usize(v_t_5824_, 4);
        v_tailOff_5832_ = crate::leanh::lean_ctor_get(v_t_5824_, 3);
        v___x_5833_ = lean_nat_dec_le(v_tailOff_5832_, v_start_5826_);
        if v___x_5833_ == 0 {
            let mut v___x_5834_: usize = 0;
            let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5837_: u8 = 0;
            v___x_5834_ = lean_usize_of_nat(v_start_5826_);
            v___x_5835_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_5823_, v_root_5829_, v___x_5834_, v_shift_5831_, v_init_5825_);
            v___x_5836_ = lean_array_get_size(v_tail_5830_);
            v___x_5837_ = lean_nat_dec_lt(v___x_5827_, v___x_5836_);
            if v___x_5837_ == 0 {
                return v___x_5835_;
            } else {
                let mut v___x_5838_: u8 = 0;
                v___x_5838_ = lean_nat_dec_le(v___x_5836_, v___x_5836_);
                if v___x_5838_ == 0 {
                    if v___x_5837_ == 0 {
                        return v___x_5835_;
                    } else {
                        let mut v___x_5839_: usize = 0;
                        let mut v___x_5840_: usize = 0;
                        let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5839_ = 0usize;
                        v___x_5840_ = lean_usize_of_nat(v___x_5836_);
                        v___x_5841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5830_, v___x_5839_, v___x_5840_, v___x_5835_);
                        return v___x_5841_;
                    }
                } else {
                    let mut v___x_5842_: usize = 0;
                    let mut v___x_5843_: usize = 0;
                    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5842_ = 0usize;
                    v___x_5843_ = lean_usize_of_nat(v___x_5836_);
                    v___x_5844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5830_, v___x_5842_, v___x_5843_, v___x_5835_);
                    return v___x_5844_;
                }
            }
        } else {
            let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5847_: u8 = 0;
            v___x_5845_ = lean_nat_sub(v_start_5826_, v_tailOff_5832_);
            v___x_5846_ = lean_array_get_size(v_tail_5830_);
            v___x_5847_ = lean_nat_dec_lt(v___x_5845_, v___x_5846_);
            if v___x_5847_ == 0 {
                crate::leanh::lean_dec(v___x_5845_);
                return v_init_5825_;
            } else {
                let mut v___x_5848_: u8 = 0;
                v___x_5848_ = lean_nat_dec_le(v___x_5846_, v___x_5846_);
                if v___x_5848_ == 0 {
                    if v___x_5847_ == 0 {
                        crate::leanh::lean_dec(v___x_5845_);
                        return v_init_5825_;
                    } else {
                        let mut v___x_5849_: usize = 0;
                        let mut v___x_5850_: usize = 0;
                        let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5849_ = lean_usize_of_nat(v___x_5845_);
                        crate::leanh::lean_dec(v___x_5845_);
                        v___x_5850_ = lean_usize_of_nat(v___x_5846_);
                        v___x_5851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5830_, v___x_5849_, v___x_5850_, v_init_5825_);
                        return v___x_5851_;
                    }
                } else {
                    let mut v___x_5852_: usize = 0;
                    let mut v___x_5853_: usize = 0;
                    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5852_ = lean_usize_of_nat(v___x_5845_);
                    crate::leanh::lean_dec(v___x_5845_);
                    v___x_5853_ = lean_usize_of_nat(v___x_5846_);
                    v___x_5854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5830_, v___x_5852_, v___x_5853_, v_init_5825_);
                    return v___x_5854_;
                }
            }
        }
    } else {
        let mut v_root_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5859_: u8 = 0;
        v_root_5855_ = crate::leanh::lean_ctor_get(v_t_5824_, 0);
        v_tail_5856_ = crate::leanh::lean_ctor_get(v_t_5824_, 1);
        v___x_5857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_5823_, v_root_5855_, v_init_5825_);
        v___x_5858_ = lean_array_get_size(v_tail_5856_);
        v___x_5859_ = lean_nat_dec_lt(v___x_5827_, v___x_5858_);
        if v___x_5859_ == 0 {
            return v___x_5857_;
        } else {
            let mut v___x_5860_: u8 = 0;
            v___x_5860_ = lean_nat_dec_le(v___x_5858_, v___x_5858_);
            if v___x_5860_ == 0 {
                if v___x_5859_ == 0 {
                    return v___x_5857_;
                } else {
                    let mut v___x_5861_: usize = 0;
                    let mut v___x_5862_: usize = 0;
                    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5861_ = 0usize;
                    v___x_5862_ = lean_usize_of_nat(v___x_5858_);
                    v___x_5863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5856_, v___x_5861_, v___x_5862_, v___x_5857_);
                    return v___x_5863_;
                }
            } else {
                let mut v___x_5864_: usize = 0;
                let mut v___x_5865_: usize = 0;
                let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5864_ = 0usize;
                v___x_5865_ = lean_usize_of_nat(v___x_5858_);
                v___x_5866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_5823_, v_tail_5856_, v___x_5864_, v___x_5865_, v___x_5857_);
                return v___x_5866_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(
    mut v_a_5867_: *mut crate::leanh::LeanObject,
    mut v_t_5868_: *mut crate::leanh::LeanObject,
    mut v_init_5869_: *mut crate::leanh::LeanObject,
    mut v_start_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_5867_, v_t_5868_, v_init_5869_, v_start_5870_);
    crate::leanh::lean_dec(v_start_5870_);
    crate::leanh::lean_dec_ref(v_t_5868_);
    crate::leanh::lean_dec_ref(v_a_5867_);
    return v_res_5871_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: u8 = 0;
    let mut v___x_5877_: f64 = 0.0;
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5875_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_5876_ = 1;
    v___x_5877_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_5878_ = crate::leanh::lean_box(0);
    v___x_5879_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1;
    v___x_5880_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_5880_, 0, v___x_5879_);
    crate::leanh::lean_ctor_set(v___x_5880_, 1, v___x_5878_);
    crate::leanh::lean_ctor_set(v___x_5880_, 2, v___x_5875_);
    crate::leanh::lean_ctor_set_float(
        v___x_5880_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5877_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_5880_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_5877_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5880_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_5876_,
    );
    return v___x_5880_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5884_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4;
    v___x_5885_ = l_Lean_MessageData_ofFormat(v___x_5884_);
    return v___x_5885_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5890_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8;
    v___x_5891_ = l_Lean_stringToMessageData(v___x_5890_);
    return v___x_5891_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5893_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10;
    v___x_5894_ = l_Lean_stringToMessageData(v___x_5893_);
    return v___x_5894_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5896_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12;
    v___x_5897_ = l_Lean_stringToMessageData(v___x_5896_);
    return v___x_5897_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5899_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14;
    v___x_5900_ = l_Lean_stringToMessageData(v___x_5899_);
    return v___x_5900_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5902_ =
        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16;
    v___x_5903_ = l_Lean_stringToMessageData(v___x_5902_);
    return v___x_5903_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(
    mut v_c_5904_: *mut crate::leanh::LeanObject,
    mut v_a_5905_: *mut crate::leanh::LeanObject,
    mut v_a_5906_: *mut crate::leanh::LeanObject,
    mut v_a_5907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_a_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v_ref_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5947_: u8 = 0;
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splits_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numInstances_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: f64 = 0.0;
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: u8 = 0;
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: f64 = 0.0;
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: f64 = 0.0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: u8 = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: f64 = 0.0;
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_5909_ = crate::leanh::lean_ctor_get(v_a_5905_, 0);
                v_exprs_5910_ = crate::leanh::lean_ctor_get(v_toGoalState_5909_, 2);
                v_ematch_5911_ = crate::leanh::lean_ctor_get(v_toGoalState_5909_, 12);
                v_split_5912_ = crate::leanh::lean_ctor_get(v_toGoalState_5909_, 14);
                v___x_5913_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5948_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_5905_, v_exprs_5910_, v___x_5913_, v___x_5913_);
                v_splits_5949_ = crate::leanh::lean_ctor_get(v_c_5904_, 0);
                v_ematch_5950_ = crate::leanh::lean_ctor_get(v_c_5904_, 1);
                v_gen_5951_ = crate::leanh::lean_ctor_get(v_c_5904_, 2);
                v_instances_5952_ = crate::leanh::lean_ctor_get(v_c_5904_, 4);
                v_numInstances_5953_ = crate::leanh::lean_ctor_get(v_ematch_5911_, 4);
                v_num_5954_ = crate::leanh::lean_ctor_get(v_ematch_5911_, 6);
                v___x_5955_ =
                    l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                v___x_6014_ = lean_nat_dec_le(v_instances_5952_, v_numInstances_5953_);
                if v___x_6014_ == 0 {
                    v_msgs_5996_ = v___x_5955_;
                    v___y_5997_ = v_a_5906_;
                    v___y_5998_ = v_a_5907_;
                    state = 8;
                    continue;
                } else {
                    v___x_6015_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7;
                    v___x_6016_ = crate::leanh::lean_box(0);
                    v___x_6017_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once), _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
                    v___x_6018_ = l_Lean_Meta_Grind_ppGoals___closed__0;
                    v___x_6019_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v___x_6019_, 0, v___x_6015_);
                    crate::leanh::lean_ctor_set(v___x_6019_, 1, v___x_6016_);
                    crate::leanh::lean_ctor_set(v___x_6019_, 2, v___x_6018_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_6019_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6017_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v___x_6019_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6017_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6019_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_6014_,
                    );
                    v___x_6020_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17);
                    crate::leanh::lean_inc(v_instances_5952_);
                    v___x_6021_ = l_Nat_reprFast(v_instances_5952_);
                    v___x_6022_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6022_, 0, v___x_6021_);
                    v___x_6023_ = l_Lean_MessageData_ofFormat(v___x_6022_);
                    v___x_6024_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6024_, 0, v___x_6020_);
                    crate::leanh::lean_ctor_set(v___x_6024_, 1, v___x_6023_);
                    v___x_6025_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
                    v___x_6026_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6026_, 0, v___x_6024_);
                    crate::leanh::lean_ctor_set(v___x_6026_, 1, v___x_6025_);
                    v___x_6027_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6027_, 0, v___x_6019_);
                    crate::leanh::lean_ctor_set(v___x_6027_, 1, v___x_6026_);
                    crate::leanh::lean_ctor_set(v___x_6027_, 2, v___x_5955_);
                    v___x_6028_ = lean_array_push(v___x_5955_, v___x_6027_);
                    v_msgs_5996_ = v___x_6028_;
                    v___y_5997_ = v_a_5906_;
                    v___y_5998_ = v_a_5907_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_5918_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(
                    v_a_5905_,
                    v_c_5904_,
                    v_msgs_5915_,
                );
                if crate::leanh::lean_obj_tag(v___x_5918_) == 0 {
                    v_a_5919_ = crate::leanh::lean_ctor_get(v___x_5918_, 0);
                    v_isSharedCheck_5934_ = (!crate::leanh::lean_is_exclusive(v___x_5918_)) as u8;
                    if v_isSharedCheck_5934_ == 0 {
                        v___x_5921_ = v___x_5918_;
                        v_isShared_5922_ = v_isSharedCheck_5934_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5919_);
                        crate::leanh::lean_dec(v___x_5918_);
                        v___x_5921_ = crate::leanh::lean_box(0);
                        v_isShared_5922_ = v_isSharedCheck_5934_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5916_);
                    v_a_5935_ = crate::leanh::lean_ctor_get(v___x_5918_, 0);
                    v_isSharedCheck_5947_ = (!crate::leanh::lean_is_exclusive(v___x_5918_)) as u8;
                    if v_isSharedCheck_5947_ == 0 {
                        v___x_5937_ = v___x_5918_;
                        v_isShared_5938_ = v_isSharedCheck_5947_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5935_);
                        crate::leanh::lean_dec(v___x_5918_);
                        v___x_5937_ = crate::leanh::lean_box(0);
                        v_isShared_5938_ = v_isSharedCheck_5947_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5923_ = lean_array_get_size(v_a_5919_);
                v___x_5924_ = lean_nat_dec_eq(v___x_5923_, v___x_5913_);
                if v___x_5924_ == 0 {
                    crate::leanh::lean_del_object(v___x_5921_);
                    v___x_5925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2);
                    v___x_5926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5);
                    v___x_5927_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5927_, 0, v___x_5925_);
                    crate::leanh::lean_ctor_set(v___x_5927_, 1, v___x_5926_);
                    crate::leanh::lean_ctor_set(v___x_5927_, 2, v_a_5919_);
                    v___x_5928_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
                            v___x_5927_,
                            v___y_5916_,
                        );
                    return v___x_5928_;
                } else {
                    crate::leanh::lean_dec(v_a_5919_);
                    v___x_5929_ = crate::leanh::lean_box(0);
                    v___x_5930_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5930_, 0, v___x_5929_);
                    crate::leanh::lean_ctor_set(v___x_5930_, 1, v___y_5916_);
                    if v_isShared_5922_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5930_);
                        v___x_5932_ = v___x_5921_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v___x_5930_);
                        v___x_5932_ = v_reuseFailAlloc_5933_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5932_;
            }
            4 => {
                v_ref_5939_ = crate::leanh::lean_ctor_get(v___y_5917_, 5);
                v___x_5940_ = lean_io_error_to_string(v_a_5935_);
                v___x_5941_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5941_, 0, v___x_5940_);
                v___x_5942_ = l_Lean_MessageData_ofFormat(v___x_5941_);
                crate::leanh::lean_inc(v_ref_5939_);
                v___x_5943_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5943_, 0, v_ref_5939_);
                crate::leanh::lean_ctor_set(v___x_5943_, 1, v___x_5942_);
                if v_isShared_5938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5937_, 0, v___x_5943_);
                    v___x_5945_ = v___x_5937_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5946_, 0, v___x_5943_);
                    v___x_5945_ = v_reuseFailAlloc_5946_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5945_;
            }
            6 => {
                v___x_5960_ = lean_nat_dec_le(v_gen_5951_, v___x_5948_);
                crate::leanh::lean_dec(v___x_5948_);
                if v___x_5960_ == 0 {
                    v_msgs_5915_ = v_msgs_5957_;
                    v___y_5916_ = v___y_5958_;
                    v___y_5917_ = v___y_5959_;
                    state = 1;
                    continue;
                } else {
                    v___x_5961_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7;
                    v___x_5962_ = crate::leanh::lean_box(0);
                    v___x_5963_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once), _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
                    v___x_5964_ = l_Lean_Meta_Grind_ppGoals___closed__0;
                    v___x_5965_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v___x_5965_, 0, v___x_5961_);
                    crate::leanh::lean_ctor_set(v___x_5965_, 1, v___x_5962_);
                    crate::leanh::lean_ctor_set(v___x_5965_, 2, v___x_5964_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_5965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_5963_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v___x_5965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5963_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_5960_,
                    );
                    v___x_5966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9);
                    crate::leanh::lean_inc(v_gen_5951_);
                    v___x_5967_ = l_Nat_reprFast(v_gen_5951_);
                    v___x_5968_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                    v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                    v___x_5970_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                    crate::leanh::lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                    v___x_5971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
                    v___x_5972_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                    crate::leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                    v___x_5973_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5973_, 0, v___x_5965_);
                    crate::leanh::lean_ctor_set(v___x_5973_, 1, v___x_5972_);
                    crate::leanh::lean_ctor_set(v___x_5973_, 2, v___x_5955_);
                    v___x_5974_ = lean_array_push(v_msgs_5957_, v___x_5973_);
                    v_msgs_5915_ = v___x_5974_;
                    v___y_5916_ = v___y_5958_;
                    v___y_5917_ = v___y_5959_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v_num_5979_ = crate::leanh::lean_ctor_get(v_split_5912_, 0);
                v___x_5980_ = lean_nat_dec_le(v_splits_5949_, v_num_5979_);
                if v___x_5980_ == 0 {
                    v_msgs_5957_ = v_msgs_5976_;
                    v___y_5958_ = v___y_5977_;
                    v___y_5959_ = v___y_5978_;
                    state = 6;
                    continue;
                } else {
                    v___x_5981_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7;
                    v___x_5982_ = crate::leanh::lean_box(0);
                    v___x_5983_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once), _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
                    v___x_5984_ = l_Lean_Meta_Grind_ppGoals___closed__0;
                    v___x_5985_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v___x_5985_, 0, v___x_5981_);
                    crate::leanh::lean_ctor_set(v___x_5985_, 1, v___x_5982_);
                    crate::leanh::lean_ctor_set(v___x_5985_, 2, v___x_5984_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_5985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_5983_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v___x_5985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5983_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_5980_,
                    );
                    v___x_5986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13);
                    crate::leanh::lean_inc(v_splits_5949_);
                    v___x_5987_ = l_Nat_reprFast(v_splits_5949_);
                    v___x_5988_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5988_, 0, v___x_5987_);
                    v___x_5989_ = l_Lean_MessageData_ofFormat(v___x_5988_);
                    v___x_5990_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5990_, 0, v___x_5986_);
                    crate::leanh::lean_ctor_set(v___x_5990_, 1, v___x_5989_);
                    v___x_5991_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
                    v___x_5992_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5992_, 0, v___x_5990_);
                    crate::leanh::lean_ctor_set(v___x_5992_, 1, v___x_5991_);
                    v___x_5993_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5993_, 0, v___x_5985_);
                    crate::leanh::lean_ctor_set(v___x_5993_, 1, v___x_5992_);
                    crate::leanh::lean_ctor_set(v___x_5993_, 2, v___x_5955_);
                    v___x_5994_ = lean_array_push(v_msgs_5976_, v___x_5993_);
                    v_msgs_5957_ = v___x_5994_;
                    v___y_5958_ = v___y_5977_;
                    v___y_5959_ = v___y_5978_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_5999_ = lean_nat_dec_le(v_ematch_5950_, v_num_5954_);
                if v___x_5999_ == 0 {
                    v_msgs_5976_ = v_msgs_5996_;
                    v___y_5977_ = v___y_5997_;
                    v___y_5978_ = v___y_5998_;
                    state = 7;
                    continue;
                } else {
                    v___x_6000_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7;
                    v___x_6001_ = crate::leanh::lean_box(0);
                    v___x_6002_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once), _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
                    v___x_6003_ = l_Lean_Meta_Grind_ppGoals___closed__0;
                    v___x_6004_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v___x_6004_, 0, v___x_6000_);
                    crate::leanh::lean_ctor_set(v___x_6004_, 1, v___x_6001_);
                    crate::leanh::lean_ctor_set(v___x_6004_, 2, v___x_6003_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_6004_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6002_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v___x_6004_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6002_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6004_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_5999_,
                    );
                    v___x_6005_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15);
                    crate::leanh::lean_inc(v_ematch_5950_);
                    v___x_6006_ = l_Nat_reprFast(v_ematch_5950_);
                    v___x_6007_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6007_, 0, v___x_6006_);
                    v___x_6008_ = l_Lean_MessageData_ofFormat(v___x_6007_);
                    v___x_6009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6009_, 0, v___x_6005_);
                    crate::leanh::lean_ctor_set(v___x_6009_, 1, v___x_6008_);
                    v___x_6010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
                    v___x_6011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6011_, 0, v___x_6009_);
                    crate::leanh::lean_ctor_set(v___x_6011_, 1, v___x_6010_);
                    v___x_6012_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6012_, 0, v___x_6004_);
                    crate::leanh::lean_ctor_set(v___x_6012_, 1, v___x_6011_);
                    crate::leanh::lean_ctor_set(v___x_6012_, 2, v___x_5955_);
                    v___x_6013_ = lean_array_push(v_msgs_5996_, v___x_6012_);
                    v_msgs_5976_ = v___x_6013_;
                    v___y_5977_ = v___y_5997_;
                    v___y_5978_ = v___y_5998_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(
    mut v_c_6029_: *mut crate::leanh::LeanObject,
    mut v_a_6030_: *mut crate::leanh::LeanObject,
    mut v_a_6031_: *mut crate::leanh::LeanObject,
    mut v_a_6032_: *mut crate::leanh::LeanObject,
    mut v_a_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(
        v_c_6029_, v_a_6030_, v_a_6031_, v_a_6032_,
    );
    crate::leanh::lean_dec_ref(v_a_6032_);
    crate::leanh::lean_dec_ref(v_a_6030_);
    return v_res_6034_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(
    mut v_c_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
    mut v_a_6037_: *mut crate::leanh::LeanObject,
    mut v_a_6038_: *mut crate::leanh::LeanObject,
    mut v_a_6039_: *mut crate::leanh::LeanObject,
    mut v_a_6040_: *mut crate::leanh::LeanObject,
    mut v_a_6041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6043_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(
        v_c_6035_, v_a_6036_, v_a_6037_, v_a_6040_,
    );
    return v___x_6043_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(
    mut v_c_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
    mut v_a_6048_: *mut crate::leanh::LeanObject,
    mut v_a_6049_: *mut crate::leanh::LeanObject,
    mut v_a_6050_: *mut crate::leanh::LeanObject,
    mut v_a_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6052_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(
        v_c_6044_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_, v_a_6049_, v_a_6050_,
    );
    crate::leanh::lean_dec(v_a_6050_);
    crate::leanh::lean_dec_ref(v_a_6049_);
    crate::leanh::lean_dec(v_a_6048_);
    crate::leanh::lean_dec_ref(v_a_6047_);
    crate::leanh::lean_dec_ref(v_a_6045_);
    return v_res_6052_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: u8 = 0;
    let mut v___x_6058_: f64 = 0.0;
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6056_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_6057_ = 1;
    v___x_6058_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_6059_ = crate::leanh::lean_box(0);
    v___x_6060_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1;
    v___x_6061_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_6061_, 0, v___x_6060_);
    crate::leanh::lean_ctor_set(v___x_6061_, 1, v___x_6059_);
    crate::leanh::lean_ctor_set(v___x_6061_, 2, v___x_6056_);
    crate::leanh::lean_ctor_set_float(
        v___x_6061_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6058_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_6061_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_6058_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6061_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_6057_,
    );
    return v___x_6061_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6063_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3;
    v___x_6064_ = l_Lean_stringToMessageData(v___x_6063_);
    return v___x_6064_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2;
    v___x_6066_ = l_Lean_stringToMessageData(v___x_6065_);
    return v___x_6066_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6068_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6;
    v___x_6069_ = l_Lean_stringToMessageData(v___x_6068_);
    return v___x_6069_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6071_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8;
    v___x_6072_ = l_Lean_stringToMessageData(v___x_6071_);
    return v___x_6072_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(
    mut v_as_x27_6073_: *mut crate::leanh::LeanObject,
    mut v_b_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6073_) == 0 {
                    v___x_6077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6077_, 0, v_b_6074_);
                    crate::leanh::lean_ctor_set(v___x_6077_, 1, v___y_6075_);
                    v___x_6078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6078_, 0, v___x_6077_);
                    return v___x_6078_;
                } else {
                    v_head_6079_ = crate::leanh::lean_ctor_get(v_as_x27_6073_, 0);
                    v_tail_6080_ = crate::leanh::lean_ctor_get(v_as_x27_6073_, 1);
                    v_expr_6081_ = crate::leanh::lean_ctor_get(v_head_6079_, 0);
                    v_i_6082_ = crate::leanh::lean_ctor_get(v_head_6079_, 1);
                    v_num_6083_ = crate::leanh::lean_ctor_get(v_head_6079_, 2);
                    v_source_6084_ = crate::leanh::lean_ctor_get(v_head_6079_, 3);
                    v___x_6085_ =
                        l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                    v___x_6086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
                    v___x_6087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4);
                    v___x_6088_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6089_ = lean_nat_add(v_i_6082_, v___x_6088_);
                    v___x_6090_ = l_Nat_reprFast(v___x_6089_);
                    v___x_6091_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6091_, 0, v___x_6090_);
                    v___x_6092_ = l_Lean_MessageData_ofFormat(v___x_6091_);
                    v___x_6093_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6093_, 0, v___x_6087_);
                    crate::leanh::lean_ctor_set(v___x_6093_, 1, v___x_6092_);
                    v___x_6094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5);
                    v___x_6095_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6095_, 0, v___x_6093_);
                    crate::leanh::lean_ctor_set(v___x_6095_, 1, v___x_6094_);
                    crate::leanh::lean_inc(v_num_6083_);
                    v___x_6096_ = l_Nat_reprFast(v_num_6083_);
                    v___x_6097_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6097_, 0, v___x_6096_);
                    v___x_6098_ = l_Lean_MessageData_ofFormat(v___x_6097_);
                    v___x_6099_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6099_, 0, v___x_6095_);
                    crate::leanh::lean_ctor_set(v___x_6099_, 1, v___x_6098_);
                    v___x_6100_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7);
                    v___x_6101_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6101_, 0, v___x_6099_);
                    crate::leanh::lean_ctor_set(v___x_6101_, 1, v___x_6100_);
                    crate::leanh::lean_inc_ref(v_expr_6081_);
                    v___x_6102_ = l_Lean_MessageData_ofExpr(v_expr_6081_);
                    v___x_6103_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6103_, 0, v___x_6101_);
                    crate::leanh::lean_ctor_set(v___x_6103_, 1, v___x_6102_);
                    v___x_6104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9);
                    crate::leanh::lean_inc(v_source_6084_);
                    v___x_6105_ = l_Lean_Meta_Grind_SplitSource_toMessageData(v_source_6084_);
                    v___x_6106_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6106_, 0, v___x_6104_);
                    crate::leanh::lean_ctor_set(v___x_6106_, 1, v___x_6105_);
                    v___x_6107_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6107_, 0, v___x_6086_);
                    crate::leanh::lean_ctor_set(v___x_6107_, 1, v___x_6106_);
                    crate::leanh::lean_ctor_set(v___x_6107_, 2, v___x_6085_);
                    v___x_6108_ = lean_mk_empty_array_with_capacity(v___x_6088_);
                    v___x_6109_ = lean_array_push(v___x_6108_, v___x_6107_);
                    v___x_6110_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6110_, 0, v___x_6086_);
                    crate::leanh::lean_ctor_set(v___x_6110_, 1, v___x_6103_);
                    crate::leanh::lean_ctor_set(v___x_6110_, 2, v___x_6109_);
                    v___x_6111_ = lean_array_push(v_b_6074_, v___x_6110_);
                    v_as_x27_6073_ = v_tail_6080_;
                    v_b_6074_ = v___x_6111_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(
    mut v_as_x27_6113_: *mut crate::leanh::LeanObject,
    mut v_b_6114_: *mut crate::leanh::LeanObject,
    mut v___y_6115_: *mut crate::leanh::LeanObject,
    mut v___y_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6117_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_6113_, v_b_6114_, v___y_6115_);
    crate::leanh::lean_dec(v_as_x27_6113_);
    return v_res_6117_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6121_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1;
    v___x_6122_ = l_Lean_MessageData_ofFormat(v___x_6121_);
    return v___x_6122_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(
    mut v_a_6123_: *mut crate::leanh::LeanObject,
    mut v_a_6124_: *mut crate::leanh::LeanObject,
    mut v_a_6125_: *mut crate::leanh::LeanObject,
    mut v_a_6126_: *mut crate::leanh::LeanObject,
    mut v_a_6127_: *mut crate::leanh::LeanObject,
    mut v_a_6128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: u8 = 0;
    v_toGoalState_6130_ = crate::leanh::lean_ctor_get(v_a_6123_, 0);
    v_split_6131_ = crate::leanh::lean_ctor_get(v_toGoalState_6130_, 14);
    v_trace_6132_ = crate::leanh::lean_ctor_get(v_split_6131_, 4);
    v___x_6133_ = l_List_isEmpty___redArg(v_trace_6132_);
    if v___x_6133_ == 0 {
        let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6134_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
        crate::leanh::lean_inc(v_trace_6132_);
        v___x_6135_ = l_List_reverse___redArg(v_trace_6132_);
        v___x_6136_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v___x_6135_, v___x_6134_, v_a_6124_);
        crate::leanh::lean_dec(v___x_6135_);
        v_a_6137_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
        crate::leanh::lean_inc(v_a_6137_);
        crate::leanh::lean_dec_ref(v___x_6136_);
        v_fst_6138_ = crate::leanh::lean_ctor_get(v_a_6137_, 0);
        crate::leanh::lean_inc(v_fst_6138_);
        v_snd_6139_ = crate::leanh::lean_ctor_get(v_a_6137_, 1);
        crate::leanh::lean_inc(v_snd_6139_);
        crate::leanh::lean_dec(v_a_6137_);
        v___x_6140_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
        v___x_6141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2);
        v___x_6142_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6140_);
        crate::leanh::lean_ctor_set(v___x_6142_, 1, v___x_6141_);
        crate::leanh::lean_ctor_set(v___x_6142_, 2, v_fst_6138_);
        v___x_6143_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
            v___x_6142_,
            v_snd_6139_,
        );
        return v___x_6143_;
    } else {
        let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6144_ = crate::leanh::lean_box(0);
        v___x_6145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6145_, 0, v___x_6144_);
        crate::leanh::lean_ctor_set(v___x_6145_, 1, v_a_6124_);
        v___x_6146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6146_, 0, v___x_6145_);
        return v___x_6146_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(
    mut v_a_6147_: *mut crate::leanh::LeanObject,
    mut v_a_6148_: *mut crate::leanh::LeanObject,
    mut v_a_6149_: *mut crate::leanh::LeanObject,
    mut v_a_6150_: *mut crate::leanh::LeanObject,
    mut v_a_6151_: *mut crate::leanh::LeanObject,
    mut v_a_6152_: *mut crate::leanh::LeanObject,
    mut v_a_6153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6154_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(
        v_a_6147_, v_a_6148_, v_a_6149_, v_a_6150_, v_a_6151_, v_a_6152_,
    );
    crate::leanh::lean_dec(v_a_6152_);
    crate::leanh::lean_dec_ref(v_a_6151_);
    crate::leanh::lean_dec(v_a_6150_);
    crate::leanh::lean_dec_ref(v_a_6149_);
    crate::leanh::lean_dec_ref(v_a_6147_);
    return v_res_6154_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(
    mut v_as_6155_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6156_: *mut crate::leanh::LeanObject,
    mut v_b_6157_: *mut crate::leanh::LeanObject,
    mut v_a_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
    mut v___y_6164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6166_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_6156_, v_b_6157_, v___y_6160_);
    return v___x_6166_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(
    mut v_as_6167_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6168_: *mut crate::leanh::LeanObject,
    mut v_b_6169_: *mut crate::leanh::LeanObject,
    mut v_a_6170_: *mut crate::leanh::LeanObject,
    mut v___y_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6178_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(v_as_6167_, v_as_x27_6168_, v_b_6169_, v_a_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
    crate::leanh::lean_dec(v___y_6176_);
    crate::leanh::lean_dec_ref(v___y_6175_);
    crate::leanh::lean_dec(v___y_6174_);
    crate::leanh::lean_dec_ref(v___y_6173_);
    crate::leanh::lean_dec_ref(v___y_6171_);
    crate::leanh::lean_dec(v_as_x27_6168_);
    crate::leanh::lean_dec(v_as_6167_);
    return v_res_6178_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(
    mut v_goal_6183_: *mut crate::leanh::LeanObject,
    mut v_config_6184_: *mut crate::leanh::LeanObject,
    mut v_collapsedMain_6185_: u8,
    mut v_a_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
    mut v_a_6190_: *mut crate::leanh::LeanObject,
    mut v_a_6191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toGoalState_6193_ = crate::leanh::lean_ctor_get(v_goal_6183_, 0);
    v_facts_6194_ = crate::leanh::lean_ctor_get(v_toGoalState_6193_, 10);
    v___x_6195_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1;
    v___x_6196_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2;
    v___x_6197_ = l_Lean_PersistentArray_toArray___redArg(v_facts_6194_);
    v___x_6198_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2;
    v___x_6199_ = l_Lean_Meta_Grind_ppExprArray(
        v___x_6195_,
        v___x_6196_,
        v___x_6197_,
        v___x_6198_,
        v_collapsedMain_6185_,
    );
    v___x_6200_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(
        v___x_6199_,
        v_a_6187_,
    );
    v_a_6201_ = crate::leanh::lean_ctor_get(v___x_6200_, 0);
    crate::leanh::lean_inc(v_a_6201_);
    crate::leanh::lean_dec_ref(v___x_6200_);
    v_snd_6202_ = crate::leanh::lean_ctor_get(v_a_6201_, 1);
    crate::leanh::lean_inc(v_snd_6202_);
    crate::leanh::lean_dec(v_a_6201_);
    v___x_6203_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(
        v_collapsedMain_6185_,
        v_a_6186_,
        v_snd_6202_,
        v_a_6188_,
        v_a_6189_,
        v_a_6190_,
        v_a_6191_,
    );
    if crate::leanh::lean_obj_tag(v___x_6203_) == 0 {
        let mut v_a_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6204_ = crate::leanh::lean_ctor_get(v___x_6203_, 0);
        crate::leanh::lean_inc(v_a_6204_);
        crate::leanh::lean_dec_ref_known(v___x_6203_, 1);
        v_snd_6205_ = crate::leanh::lean_ctor_get(v_a_6204_, 1);
        crate::leanh::lean_inc(v_snd_6205_);
        crate::leanh::lean_dec(v_a_6204_);
        v___x_6206_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(
            v_a_6186_,
            v_snd_6205_,
            v_a_6188_,
            v_a_6189_,
            v_a_6190_,
            v_a_6191_,
        );
        if crate::leanh::lean_obj_tag(v___x_6206_) == 0 {
            let mut v_a_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6207_ = crate::leanh::lean_ctor_get(v___x_6206_, 0);
            crate::leanh::lean_inc(v_a_6207_);
            crate::leanh::lean_dec_ref_known(v___x_6206_, 1);
            v_snd_6208_ = crate::leanh::lean_ctor_get(v_a_6207_, 1);
            crate::leanh::lean_inc(v_snd_6208_);
            crate::leanh::lean_dec(v_a_6207_);
            v___x_6209_ =
                l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(
                    v_a_6186_,
                    v_snd_6208_,
                    v_a_6188_,
                    v_a_6189_,
                    v_a_6190_,
                    v_a_6191_,
                );
            if crate::leanh::lean_obj_tag(v___x_6209_) == 0 {
                let mut v_a_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_snd_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_6210_ = crate::leanh::lean_ctor_get(v___x_6209_, 0);
                crate::leanh::lean_inc(v_a_6210_);
                crate::leanh::lean_dec_ref_known(v___x_6209_, 1);
                v_snd_6211_ = crate::leanh::lean_ctor_get(v_a_6210_, 1);
                crate::leanh::lean_inc(v_snd_6211_);
                crate::leanh::lean_dec(v_a_6210_);
                v___x_6212_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(
                    v_a_6186_,
                    v_snd_6211_,
                    v_a_6188_,
                    v_a_6189_,
                    v_a_6190_,
                    v_a_6191_,
                );
                if crate::leanh::lean_obj_tag(v___x_6212_) == 0 {
                    let mut v_a_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_6213_ = crate::leanh::lean_ctor_get(v___x_6212_, 0);
                    crate::leanh::lean_inc(v_a_6213_);
                    crate::leanh::lean_dec_ref_known(v___x_6212_, 1);
                    v_snd_6214_ = crate::leanh::lean_ctor_get(v_a_6213_, 1);
                    crate::leanh::lean_inc(v_snd_6214_);
                    crate::leanh::lean_dec(v_a_6213_);
                    v___x_6215_ =
                        l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(
                            v_a_6186_,
                            v_snd_6214_,
                            v_a_6188_,
                            v_a_6189_,
                            v_a_6190_,
                            v_a_6191_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6215_) == 0 {
                        let mut v_a_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_6216_ = crate::leanh::lean_ctor_get(v___x_6215_, 0);
                        crate::leanh::lean_inc(v_a_6216_);
                        crate::leanh::lean_dec_ref_known(v___x_6215_, 1);
                        v_snd_6217_ = crate::leanh::lean_ctor_get(v_a_6216_, 1);
                        crate::leanh::lean_inc(v_snd_6217_);
                        crate::leanh::lean_dec(v_a_6216_);
                        v___x_6218_ =
                            l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(
                                v_a_6186_,
                                v_snd_6217_,
                                v_a_6188_,
                                v_a_6189_,
                                v_a_6190_,
                                v_a_6191_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6218_) == 0 {
                            let mut v_a_6219_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_snd_6220_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6221_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_a_6219_ = crate::leanh::lean_ctor_get(v___x_6218_, 0);
                            crate::leanh::lean_inc(v_a_6219_);
                            crate::leanh::lean_dec_ref_known(v___x_6218_, 1);
                            v_snd_6220_ = crate::leanh::lean_ctor_get(v_a_6219_, 1);
                            crate::leanh::lean_inc(v_snd_6220_);
                            crate::leanh::lean_dec(v_a_6219_);
                            v___x_6221_ =
                                l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(
                                    v_a_6186_,
                                    v_snd_6220_,
                                    v_a_6188_,
                                    v_a_6189_,
                                    v_a_6190_,
                                    v_a_6191_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_6221_) == 0 {
                                let mut v_a_6222_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_snd_6223_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6224_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_a_6222_ = crate::leanh::lean_ctor_get(v___x_6221_, 0);
                                crate::leanh::lean_inc(v_a_6222_);
                                crate::leanh::lean_dec_ref_known(v___x_6221_, 1);
                                v_snd_6223_ = crate::leanh::lean_ctor_get(v_a_6222_, 1);
                                crate::leanh::lean_inc(v_snd_6223_);
                                crate::leanh::lean_dec(v_a_6222_);
                                v___x_6224_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_config_6184_, v_a_6186_, v_snd_6223_, v_a_6190_);
                                return v___x_6224_;
                            } else {
                                crate::leanh::lean_dec_ref(v_config_6184_);
                                return v___x_6221_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_config_6184_);
                            return v___x_6218_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_config_6184_);
                        return v___x_6215_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_6184_);
                    return v___x_6212_;
                }
            } else {
                crate::leanh::lean_dec_ref(v_config_6184_);
                return v___x_6209_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_config_6184_);
            return v___x_6206_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_config_6184_);
        return v___x_6203_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(
    mut v_goal_6225_: *mut crate::leanh::LeanObject,
    mut v_config_6226_: *mut crate::leanh::LeanObject,
    mut v_collapsedMain_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_a_6229_: *mut crate::leanh::LeanObject,
    mut v_a_6230_: *mut crate::leanh::LeanObject,
    mut v_a_6231_: *mut crate::leanh::LeanObject,
    mut v_a_6232_: *mut crate::leanh::LeanObject,
    mut v_a_6233_: *mut crate::leanh::LeanObject,
    mut v_a_6234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsedMain_boxed_6235_: u8 = 0;
    let mut v_res_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsedMain_boxed_6235_ = (crate::leanh::lean_unbox(v_collapsedMain_6227_) as u8);
    v_res_6236_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(
        v_goal_6225_,
        v_config_6226_,
        v_collapsedMain_boxed_6235_,
        v_a_6228_,
        v_a_6229_,
        v_a_6230_,
        v_a_6231_,
        v_a_6232_,
        v_a_6233_,
    );
    crate::leanh::lean_dec(v_a_6233_);
    crate::leanh::lean_dec_ref(v_a_6232_);
    crate::leanh::lean_dec(v_a_6231_);
    crate::leanh::lean_dec_ref(v_a_6230_);
    crate::leanh::lean_dec_ref(v_a_6228_);
    crate::leanh::lean_dec_ref(v_goal_6225_);
    return v_res_6236_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: u8 = 0;
    let mut v___x_6242_: f64 = 0.0;
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6240_ = l_Lean_Meta_Grind_ppGoals___closed__0;
    v___x_6241_ = 0;
    v___x_6242_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once
        ),
        _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0,
    );
    v___x_6243_ = crate::leanh::lean_box(0);
    v___x_6244_ = l_Lean_Meta_Grind_goalDiagToMessageData___closed__1;
    v___x_6245_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_6245_, 0, v___x_6244_);
    crate::leanh::lean_ctor_set(v___x_6245_, 1, v___x_6243_);
    crate::leanh::lean_ctor_set(v___x_6245_, 2, v___x_6240_);
    crate::leanh::lean_ctor_set_float(
        v___x_6245_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6242_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_6245_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_6242_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6245_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_6241_,
    );
    return v___x_6245_;
}
pub unsafe fn l_Lean_Meta_Grind_goalDiagToMessageData(
    mut v_goal_6246_: *mut crate::leanh::LeanObject,
    mut v_config_6247_: *mut crate::leanh::LeanObject,
    mut v_header_6248_: *mut crate::leanh::LeanObject,
    mut v_collapsedMain_6249_: u8,
    mut v_a_6250_: *mut crate::leanh::LeanObject,
    mut v_a_6251_: *mut crate::leanh::LeanObject,
    mut v_a_6252_: *mut crate::leanh::LeanObject,
    mut v_a_6253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v_snd_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_a_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6255_ =
                    l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1;
                v___x_6256_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_6246_, v_config_6247_, v_collapsedMain_6249_, v_goal_6246_, v___x_6255_, v_a_6250_, v_a_6251_, v_a_6252_, v_a_6253_);
                if crate::leanh::lean_obj_tag(v___x_6256_) == 0 {
                    v_a_6257_ = crate::leanh::lean_ctor_get(v___x_6256_, 0);
                    v_isSharedCheck_6269_ = (!crate::leanh::lean_is_exclusive(v___x_6256_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6259_ = v___x_6256_;
                        v_isShared_6260_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6257_);
                        crate::leanh::lean_dec(v___x_6256_);
                        v___x_6259_ = crate::leanh::lean_box(0);
                        v_isShared_6260_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_header_6248_);
                    v_a_6270_ = crate::leanh::lean_ctor_get(v___x_6256_, 0);
                    v_isSharedCheck_6277_ = (!crate::leanh::lean_is_exclusive(v___x_6256_)) as u8;
                    if v_isSharedCheck_6277_ == 0 {
                        v___x_6272_ = v___x_6256_;
                        v_isShared_6273_ = v_isSharedCheck_6277_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6270_);
                        crate::leanh::lean_dec(v___x_6256_);
                        v___x_6272_ = crate::leanh::lean_box(0);
                        v_isShared_6273_ = v_isSharedCheck_6277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6261_ = crate::leanh::lean_ctor_get(v_a_6257_, 1);
                crate::leanh::lean_inc(v_snd_6261_);
                crate::leanh::lean_dec(v_a_6257_);
                v___x_6262_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_goalDiagToMessageData___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once
                    ),
                    _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2,
                );
                v___x_6263_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6263_, 0, v_header_6248_);
                v___x_6264_ = l_Lean_MessageData_ofFormat(v___x_6263_);
                v___x_6265_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6265_, 0, v___x_6262_);
                crate::leanh::lean_ctor_set(v___x_6265_, 1, v___x_6264_);
                crate::leanh::lean_ctor_set(v___x_6265_, 2, v_snd_6261_);
                if v_isShared_6260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6259_, 0, v___x_6265_);
                    v___x_6267_ = v___x_6259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6265_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6267_;
            }
            3 => {
                if v_isShared_6273_ == 0 {
                    v___x_6275_ = v___x_6272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_a_6270_);
                    v___x_6275_ = v_reuseFailAlloc_6276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_goalDiagToMessageData___boxed(
    mut v_goal_6278_: *mut crate::leanh::LeanObject,
    mut v_config_6279_: *mut crate::leanh::LeanObject,
    mut v_header_6280_: *mut crate::leanh::LeanObject,
    mut v_collapsedMain_6281_: *mut crate::leanh::LeanObject,
    mut v_a_6282_: *mut crate::leanh::LeanObject,
    mut v_a_6283_: *mut crate::leanh::LeanObject,
    mut v_a_6284_: *mut crate::leanh::LeanObject,
    mut v_a_6285_: *mut crate::leanh::LeanObject,
    mut v_a_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsedMain_boxed_6287_: u8 = 0;
    let mut v_res_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsedMain_boxed_6287_ = (crate::leanh::lean_unbox(v_collapsedMain_6281_) as u8);
    v_res_6288_ = l_Lean_Meta_Grind_goalDiagToMessageData(
        v_goal_6278_,
        v_config_6279_,
        v_header_6280_,
        v_collapsedMain_boxed_6287_,
        v_a_6282_,
        v_a_6283_,
        v_a_6284_,
        v_a_6285_,
    );
    crate::leanh::lean_dec(v_a_6285_);
    crate::leanh::lean_dec_ref(v_a_6284_);
    crate::leanh::lean_dec(v_a_6283_);
    crate::leanh::lean_dec_ref(v_a_6282_);
    crate::leanh::lean_dec_ref(v_goal_6278_);
    return v_res_6288_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(
    mut v_msgData_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6295_ = lean_st_ref_get(v___y_6293_);
    v_env_6296_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
    crate::leanh::lean_inc_ref(v_env_6296_);
    crate::leanh::lean_dec(v___x_6295_);
    v___x_6297_ = lean_st_ref_get(v___y_6291_);
    v_mctx_6298_ = crate::leanh::lean_ctor_get(v___x_6297_, 0);
    crate::leanh::lean_inc_ref(v_mctx_6298_);
    crate::leanh::lean_dec(v___x_6297_);
    v_lctx_6299_ = crate::leanh::lean_ctor_get(v___y_6290_, 2);
    v_options_6300_ = crate::leanh::lean_ctor_get(v___y_6292_, 2);
    crate::leanh::lean_inc_ref(v_options_6300_);
    crate::leanh::lean_inc_ref(v_lctx_6299_);
    v___x_6301_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6301_, 0, v_env_6296_);
    crate::leanh::lean_ctor_set(v___x_6301_, 1, v_mctx_6298_);
    crate::leanh::lean_ctor_set(v___x_6301_, 2, v_lctx_6299_);
    crate::leanh::lean_ctor_set(v___x_6301_, 3, v_options_6300_);
    v___x_6302_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6302_, 0, v___x_6301_);
    crate::leanh::lean_ctor_set(v___x_6302_, 1, v_msgData_6289_);
    v___x_6303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6303_, 0, v___x_6302_);
    return v___x_6303_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(
    mut v_msgData_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6310_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(
        v_msgData_6304_,
        v___y_6305_,
        v___y_6306_,
        v___y_6307_,
        v___y_6308_,
    );
    crate::leanh::lean_dec(v___y_6308_);
    crate::leanh::lean_dec_ref(v___y_6307_);
    crate::leanh::lean_dec(v___y_6306_);
    crate::leanh::lean_dec_ref(v___y_6305_);
    return v_res_6310_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(
    mut v_mvarId_6311_: *mut crate::leanh::LeanObject,
    mut v_x_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6326_: u8 = 0;
    let mut v_a_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6330_: u8 = 0;
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_6311_,
                    v_x_6312_,
                    v___y_6313_,
                    v___y_6314_,
                    v___y_6315_,
                    v___y_6316_,
                );
                if crate::leanh::lean_obj_tag(v___x_6318_) == 0 {
                    v_a_6319_ = crate::leanh::lean_ctor_get(v___x_6318_, 0);
                    v_isSharedCheck_6326_ = (!crate::leanh::lean_is_exclusive(v___x_6318_)) as u8;
                    if v_isSharedCheck_6326_ == 0 {
                        v___x_6321_ = v___x_6318_;
                        v_isShared_6322_ = v_isSharedCheck_6326_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6319_);
                        crate::leanh::lean_dec(v___x_6318_);
                        v___x_6321_ = crate::leanh::lean_box(0);
                        v_isShared_6322_ = v_isSharedCheck_6326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6327_ = crate::leanh::lean_ctor_get(v___x_6318_, 0);
                    v_isSharedCheck_6334_ = (!crate::leanh::lean_is_exclusive(v___x_6318_)) as u8;
                    if v_isSharedCheck_6334_ == 0 {
                        v___x_6329_ = v___x_6318_;
                        v_isShared_6330_ = v_isSharedCheck_6334_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6327_);
                        crate::leanh::lean_dec(v___x_6318_);
                        v___x_6329_ = crate::leanh::lean_box(0);
                        v_isShared_6330_ = v_isSharedCheck_6334_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6322_ == 0 {
                    v___x_6324_ = v___x_6321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_a_6319_);
                    v___x_6324_ = v_reuseFailAlloc_6325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6324_;
            }
            3 => {
                if v_isShared_6330_ == 0 {
                    v___x_6332_ = v___x_6329_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_a_6327_);
                    v___x_6332_ = v_reuseFailAlloc_6333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(
    mut v_mvarId_6335_: *mut crate::leanh::LeanObject,
    mut v_x_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6342_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(
            v_mvarId_6335_,
            v_x_6336_,
            v___y_6337_,
            v___y_6338_,
            v___y_6339_,
            v___y_6340_,
        );
    crate::leanh::lean_dec(v___y_6340_);
    crate::leanh::lean_dec_ref(v___y_6339_);
    crate::leanh::lean_dec(v___y_6338_);
    crate::leanh::lean_dec_ref(v___y_6337_);
    return v_res_6342_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(
    mut v_00_u03b1_6343_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6344_: *mut crate::leanh::LeanObject,
    mut v_x_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
    mut v___y_6347_: *mut crate::leanh::LeanObject,
    mut v___y_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6351_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(
            v_mvarId_6344_,
            v_x_6345_,
            v___y_6346_,
            v___y_6347_,
            v___y_6348_,
            v___y_6349_,
        );
    return v___x_6351_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(
    mut v_00_u03b1_6352_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6353_: *mut crate::leanh::LeanObject,
    mut v_x_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
    mut v___y_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6360_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(
        v_00_u03b1_6352_,
        v_mvarId_6353_,
        v_x_6354_,
        v___y_6355_,
        v___y_6356_,
        v___y_6357_,
        v___y_6358_,
    );
    crate::leanh::lean_dec(v___y_6358_);
    crate::leanh::lean_dec_ref(v___y_6357_);
    crate::leanh::lean_dec(v___y_6356_);
    crate::leanh::lean_dec_ref(v___y_6355_);
    return v_res_6360_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6362_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0;
    v___x_6363_ = l_Lean_stringToMessageData(v___x_6362_);
    return v___x_6363_;
}
pub unsafe fn l_Lean_Meta_Grind_goalToMessageData___lam__0(
    mut v_verbose_6364_: u8,
    mut v_mvarId_6365_: *mut crate::leanh::LeanObject,
    mut v_goal_6366_: *mut crate::leanh::LeanObject,
    mut v_config_6367_: *mut crate::leanh::LeanObject,
    mut v___x_6368_: u8,
    mut v___y_6369_: *mut crate::leanh::LeanObject,
    mut v___y_6370_: *mut crate::leanh::LeanObject,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
    mut v___y_6372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_verbose_6364_ == 0 {
                    crate::leanh::lean_dec_ref(v_config_6367_);
                    v___x_6374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6374_, 0, v_mvarId_6365_);
                    v___x_6375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6375_, 0, v___x_6374_);
                    return v___x_6375_;
                } else {
                    v___x_6376_ = l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0;
                    v___x_6377_ = l_Lean_Meta_Grind_goalDiagToMessageData(
                        v_goal_6366_,
                        v_config_6367_,
                        v___x_6376_,
                        v___x_6368_,
                        v___y_6369_,
                        v___y_6370_,
                        v___y_6371_,
                        v___y_6372_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6377_) == 0 {
                        v_a_6378_ = crate::leanh::lean_ctor_get(v___x_6377_, 0);
                        v_isSharedCheck_6389_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6377_)) as u8;
                        if v_isSharedCheck_6389_ == 0 {
                            v___x_6380_ = v___x_6377_;
                            v_isShared_6381_ = v_isSharedCheck_6389_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6378_);
                            crate::leanh::lean_dec(v___x_6377_);
                            v___x_6380_ = crate::leanh::lean_box(0);
                            v_isShared_6381_ = v_isSharedCheck_6389_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_6365_);
                        return v___x_6377_;
                    }
                }
            }
            1 => {
                if v_isShared_6381_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6380_, 1);
                    crate::leanh::lean_ctor_set(v___x_6380_, 0, v_mvarId_6365_);
                    v___x_6383_ = v___x_6380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_mvarId_6365_);
                    v___x_6383_ = v_reuseFailAlloc_6388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6384_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1,
                );
                v___x_6385_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6385_, 0, v___x_6383_);
                crate::leanh::lean_ctor_set(v___x_6385_, 1, v___x_6384_);
                v___x_6386_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6386_, 0, v___x_6385_);
                crate::leanh::lean_ctor_set(v___x_6386_, 1, v_a_6378_);
                v___x_6387_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(
                        v___x_6386_,
                        v___y_6369_,
                        v___y_6370_,
                        v___y_6371_,
                        v___y_6372_,
                    );
                return v___x_6387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(
    mut v_verbose_6390_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6391_: *mut crate::leanh::LeanObject,
    mut v_goal_6392_: *mut crate::leanh::LeanObject,
    mut v_config_6393_: *mut crate::leanh::LeanObject,
    mut v___x_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_verbose_boxed_6400_: u8 = 0;
    let mut v___x_1179__boxed_6401_: u8 = 0;
    let mut v_res_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_verbose_boxed_6400_ = (crate::leanh::lean_unbox(v_verbose_6390_) as u8);
    v___x_1179__boxed_6401_ = (crate::leanh::lean_unbox(v___x_6394_) as u8);
    v_res_6402_ = l_Lean_Meta_Grind_goalToMessageData___lam__0(
        v_verbose_boxed_6400_,
        v_mvarId_6391_,
        v_goal_6392_,
        v_config_6393_,
        v___x_1179__boxed_6401_,
        v___y_6395_,
        v___y_6396_,
        v___y_6397_,
        v___y_6398_,
    );
    crate::leanh::lean_dec(v___y_6398_);
    crate::leanh::lean_dec_ref(v___y_6397_);
    crate::leanh::lean_dec(v___y_6396_);
    crate::leanh::lean_dec_ref(v___y_6395_);
    crate::leanh::lean_dec_ref(v_goal_6392_);
    return v_res_6402_;
}
pub unsafe fn l_Lean_Meta_Grind_goalToMessageData(
    mut v_goal_6403_: *mut crate::leanh::LeanObject,
    mut v_config_6404_: *mut crate::leanh::LeanObject,
    mut v_a_6405_: *mut crate::leanh::LeanObject,
    mut v_a_6406_: *mut crate::leanh::LeanObject,
    mut v_a_6407_: *mut crate::leanh::LeanObject,
    mut v_a_6408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_verbose_6410_: u8 = 0;
    let mut v_mvarId_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: u8 = 0;
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_verbose_6410_ = crate::leanh::lean_ctor_get_uint8(
        v_config_6404_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 15) as u32,
    );
    v_mvarId_6411_ = crate::leanh::lean_ctor_get(v_goal_6403_, 1);
    crate::leanh::lean_inc_n(v_mvarId_6411_, 2);
    v___x_6412_ = 1;
    v___x_6413_ = crate::leanh::lean_box((v_verbose_6410_) as usize);
    v___x_6414_ = crate::leanh::lean_box((v___x_6412_) as usize);
    v___y_6415_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___y_6415_, 0, v___x_6413_);
    crate::leanh::lean_closure_set(v___y_6415_, 1, v_mvarId_6411_);
    crate::leanh::lean_closure_set(v___y_6415_, 2, v_goal_6403_);
    crate::leanh::lean_closure_set(v___y_6415_, 3, v_config_6404_);
    crate::leanh::lean_closure_set(v___y_6415_, 4, v___x_6414_);
    v___x_6416_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(
            v_mvarId_6411_,
            v___y_6415_,
            v_a_6405_,
            v_a_6406_,
            v_a_6407_,
            v_a_6408_,
        );
    return v___x_6416_;
}
pub unsafe fn l_Lean_Meta_Grind_goalToMessageData___boxed(
    mut v_goal_6417_: *mut crate::leanh::LeanObject,
    mut v_config_6418_: *mut crate::leanh::LeanObject,
    mut v_a_6419_: *mut crate::leanh::LeanObject,
    mut v_a_6420_: *mut crate::leanh::LeanObject,
    mut v_a_6421_: *mut crate::leanh::LeanObject,
    mut v_a_6422_: *mut crate::leanh::LeanObject,
    mut v_a_6423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6424_ = l_Lean_Meta_Grind_goalToMessageData(
        v_goal_6417_,
        v_config_6418_,
        v_a_6419_,
        v_a_6420_,
        v_a_6421_,
        v_a_6422_,
    );
    crate::leanh::lean_dec(v_a_6422_);
    crate::leanh::lean_dec_ref(v_a_6421_);
    crate::leanh::lean_dec(v_a_6420_);
    crate::leanh::lean_dec_ref(v_a_6419_);
    return v_res_6424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_PP(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_instInhabitedResult_default =
        _init_l_Lean_Meta_Grind_instInhabitedResult_default();
    l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult =
        _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_PP(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_PP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_PP(builtin);
}
