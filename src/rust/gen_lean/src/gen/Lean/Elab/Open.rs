// Lean compiler output
// Module: Lean.Elab.Open
// Imports: Lean.Elab.Util Lean.Parser.Command Lean.Parser.Command Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_get___boxed, l_StateRefT_x27_instMonad___aux__13___boxed,
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_zip___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_mapTR_loop___redArg;
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Option::Basic::{
    l_Option_bind, l_instFunctorOption___lam__0, l_instMonadOption___lam__0,
    l_instMonadOption___lam__1, l_instMonadOption___lam__2___boxed,
    l_instMonadOption___lam__3___boxed,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_TSyntax_getId, l_Lean_TSyntax_getId___boxed};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind,
    l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg, l_Lean_replaceRef,
    l_List_lengthTR___redArg, l_Option_map, l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_throwUnsupportedSyntax___redArg;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_addConstInfo___redArg;
use crate::r#gen::Lean::Elab::InfoTree::Types::l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg;
use crate::r#gen::Lean::Elab::Util::{
    initialize_Lean_Elab_Util, l_Lean_Elab_throwErrorWithNestedErrors___redArg,
    runtime_initialize_Lean_Elab_Util,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_instMonadEnvOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwError___redArg,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Log::l_Lean_instMonadLogOfMonadLift___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::ResolveName::{
    l_Lean_resolveGlobalConstNoOverloadCore___redArg, l_Lean_resolveNamespace___redArg,
    l_Lean_resolveUniqueNamespace___redArg,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_activateScoped___redArg;
use crate::ffi::lean_array_size;
use crate::ffi::lean_usize_of_nat;
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt,
};
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_MessageData_ofExpr as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 111, 112, 101, 110, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value:
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
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value:
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
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value:
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
        111, 112, 101, 110, 82, 101, 110, 97, 109, 105, 110, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value:
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value:
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value:
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
    m_data: [111, 112, 101, 110, 83, 99, 111, 112, 101, 100, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value:
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
    m_data: [111, 112, 101, 110, 79, 110, 108, 121, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value:
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
    m_data: [111, 112, 101, 110, 72, 105, 100, 105, 110, 103, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 112, 101, 110, 82, 101, 110, 97, 109, 105, 110, 103, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value:
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
    m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value:
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
    m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value:
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
    m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value:
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
    m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value:
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
    m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value:
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
    m_fun: l_Option_map as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value:
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
    m_fun: l_Option_bind as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value:
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
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
pub static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value:
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
    m_data: [111, 112, 101, 110, 83, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1:
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2:
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value:
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
            as *mut crate::leanh::LeanObject,
        4840083868155834027 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value:
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
    m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value:
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
    m_fun: l_Lean_TSyntax_getId___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = crate::leanh::lean_ctor_get(v_inst_1876_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1879_);
    crate::leanh::lean_dec_ref(v_inst_1876_);
    v_currNamespace_1880_ = crate::leanh::lean_ctor_get(v_____do__lift_1877_, 1);
    crate::leanh::lean_inc(v_currNamespace_1880_);
    crate::leanh::lean_dec_ref(v_____do__lift_1877_);
    v_toPure_1881_ = crate::leanh::lean_ctor_get(v_toApplicative_1879_, 1);
    crate::leanh::lean_inc(v_toPure_1881_);
    crate::leanh::lean_dec_ref(v_toApplicative_1879_);
    v___x_1882_ = crate::leanh::lean_apply_2(
        v_toPure_1881_,
        crate::leanh::lean_box(0),
        v_currNamespace_1880_,
    );
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
        v_inst_1883_,
        v_____do__lift_1884_,
        v___y_1885_,
    );
    crate::leanh::lean_dec(v___y_1885_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1890_ = crate::leanh::lean_ctor_get(v_inst_1887_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1890_);
    crate::leanh::lean_dec_ref(v_inst_1887_);
    v_openDecls_1891_ = crate::leanh::lean_ctor_get(v_____do__lift_1888_, 0);
    crate::leanh::lean_inc(v_openDecls_1891_);
    crate::leanh::lean_dec_ref(v_____do__lift_1888_);
    v_toPure_1892_ = crate::leanh::lean_ctor_get(v_toApplicative_1890_, 1);
    crate::leanh::lean_inc(v_toPure_1892_);
    crate::leanh::lean_dec_ref(v_toApplicative_1890_);
    v___x_1893_ =
        crate::leanh::lean_apply_2(v_toPure_1892_, crate::leanh::lean_box(0), v_openDecls_1891_);
    return v___x_1893_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(
    mut v_inst_1894_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
        v_inst_1894_,
        v_____do__lift_1895_,
        v___y_1896_,
    );
    crate::leanh::lean_dec(v___y_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
    mut v_inst_1898_: *mut crate::leanh::LeanObject,
    mut v_inst_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1898_, 3);
    v___f_1900_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1900_, 0, v_inst_1898_);
    v___f_1901_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1901_, 0, v_inst_1898_);
    v___x_1902_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1902_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1902_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1902_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1902_, 3, v_inst_1899_);
    crate::leanh::lean_inc_ref(v___x_1902_);
    v___x_1903_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_1903_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1903_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1903_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1903_, 3, v_inst_1898_);
    crate::leanh::lean_closure_set(v___x_1903_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1903_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1903_, 6, v___x_1902_);
    crate::leanh::lean_closure_set(v___x_1903_, 7, v___f_1900_);
    v___x_1904_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_1904_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1904_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1904_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1904_, 3, v_inst_1898_);
    crate::leanh::lean_closure_set(v___x_1904_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1904_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1904_, 6, v___x_1902_);
    crate::leanh::lean_closure_set(v___x_1904_, 7, v___f_1901_);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1903_);
    crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM(
    mut v_m_1906_: *mut crate::leanh::LeanObject,
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1907_, v_inst_1908_);
    return v___x_1909_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
    mut v_idStx_1910_: *mut crate::leanh::LeanObject,
    mut v_withRef_1911_: *mut crate::leanh::LeanObject,
    mut v___x_1912_: *mut crate::leanh::LeanObject,
    mut v_oldRef_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1914_ = l_Lean_replaceRef(v_idStx_1910_, v_oldRef_1913_);
    v___x_1915_ = crate::leanh::lean_apply_3(
        v_withRef_1911_,
        crate::leanh::lean_box(0),
        v_ref_1914_,
        v___x_1912_,
    );
    return v___x_1915_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(
    mut v_idStx_1916_: *mut crate::leanh::LeanObject,
    mut v_withRef_1917_: *mut crate::leanh::LeanObject,
    mut v___x_1918_: *mut crate::leanh::LeanObject,
    mut v_oldRef_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
        v_idStx_1916_,
        v_withRef_1917_,
        v___x_1918_,
        v_oldRef_1919_,
    );
    crate::leanh::lean_dec(v_oldRef_1919_);
    crate::leanh::lean_dec(v_idStx_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(
    mut v_declName_1921_: *mut crate::leanh::LeanObject,
    mut v_inst_1922_: *mut crate::leanh::LeanObject,
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_inst_1924_: *mut crate::leanh::LeanObject,
    mut v_inst_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
    mut v_inst_1928_: *mut crate::leanh::LeanObject,
    mut v_inst_1929_: *mut crate::leanh::LeanObject,
    mut v_inst_1930_: *mut crate::leanh::LeanObject,
    mut v_idStx_1931_: *mut crate::leanh::LeanObject,
    mut v_toBind_1932_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1933_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    v___x_1935_ = 1;
    crate::leanh::lean_inc(v_declName_1921_);
    v___x_1936_ = l_Lean_Environment_contains(v_____do__lift_1934_, v_declName_1921_, v___x_1935_);
    if v___x_1936_ == 0 {
        let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getRef_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_withRef_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_1933_);
        crate::leanh::lean_inc_ref(v_inst_1923_);
        v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1937_, 0, v_inst_1922_);
        crate::leanh::lean_ctor_set(v___x_1937_, 1, v_inst_1923_);
        crate::leanh::lean_ctor_set(v___x_1937_, 2, v_inst_1924_);
        v_getRef_1938_ = crate::leanh::lean_ctor_get(v_inst_1923_, 0);
        crate::leanh::lean_inc(v_getRef_1938_);
        v_withRef_1939_ = crate::leanh::lean_ctor_get(v_inst_1923_, 1);
        crate::leanh::lean_inc(v_withRef_1939_);
        crate::leanh::lean_dec_ref(v_inst_1923_);
        v___x_1940_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(
            v_inst_1925_,
            v_inst_1926_,
            v_inst_1927_,
            v_inst_1928_,
            v_inst_1929_,
            v_inst_1930_,
            v___x_1937_,
            v_declName_1921_,
        );
        v___f_1941_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1941_, 0, v_idStx_1931_);
        crate::leanh::lean_closure_set(v___f_1941_, 1, v_withRef_1939_);
        crate::leanh::lean_closure_set(v___f_1941_, 2, v___x_1940_);
        v___x_1942_ = crate::leanh::lean_apply_4(
            v_toBind_1932_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getRef_1938_,
            v___f_1941_,
        );
        return v___x_1942_;
    } else {
        let mut v_toPure_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_1932_);
        crate::leanh::lean_dec(v_idStx_1931_);
        crate::leanh::lean_dec(v_inst_1930_);
        crate::leanh::lean_dec_ref(v_inst_1929_);
        crate::leanh::lean_dec(v_inst_1928_);
        crate::leanh::lean_dec_ref(v_inst_1927_);
        crate::leanh::lean_dec_ref(v_inst_1926_);
        crate::leanh::lean_dec_ref(v_inst_1925_);
        crate::leanh::lean_dec(v_inst_1924_);
        crate::leanh::lean_dec_ref(v_inst_1923_);
        crate::leanh::lean_dec_ref(v_inst_1922_);
        v_toPure_1943_ = crate::leanh::lean_ctor_get(v_toApplicative_1933_, 1);
        crate::leanh::lean_inc(v_toPure_1943_);
        crate::leanh::lean_dec_ref(v_toApplicative_1933_);
        v___x_1944_ =
            crate::leanh::lean_apply_2(v_toPure_1943_, crate::leanh::lean_box(0), v_declName_1921_);
        return v___x_1944_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg(
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_inst_1947_: *mut crate::leanh::LeanObject,
    mut v_inst_1948_: *mut crate::leanh::LeanObject,
    mut v_inst_1949_: *mut crate::leanh::LeanObject,
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
    mut v_inst_1951_: *mut crate::leanh::LeanObject,
    mut v_inst_1952_: *mut crate::leanh::LeanObject,
    mut v_inst_1953_: *mut crate::leanh::LeanObject,
    mut v_ns_1954_: *mut crate::leanh::LeanObject,
    mut v_idStx_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1956_ = crate::leanh::lean_ctor_get(v_inst_1945_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1956_);
    v_toBind_1957_ = crate::leanh::lean_ctor_get(v_inst_1945_, 1);
    crate::leanh::lean_inc_n(v_toBind_1957_, 2);
    v_getEnv_1958_ = crate::leanh::lean_ctor_get(v_inst_1946_, 0);
    crate::leanh::lean_inc(v_getEnv_1958_);
    v___x_1959_ = l_Lean_Syntax_getId(v_idStx_1955_);
    v_declName_1960_ = l_Lean_Name_append(v_ns_1954_, v___x_1959_);
    v___f_1961_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_1961_, 0, v_declName_1960_);
    crate::leanh::lean_closure_set(v___f_1961_, 1, v_inst_1947_);
    crate::leanh::lean_closure_set(v___f_1961_, 2, v_inst_1948_);
    crate::leanh::lean_closure_set(v___f_1961_, 3, v_inst_1949_);
    crate::leanh::lean_closure_set(v___f_1961_, 4, v_inst_1945_);
    crate::leanh::lean_closure_set(v___f_1961_, 5, v_inst_1953_);
    crate::leanh::lean_closure_set(v___f_1961_, 6, v_inst_1946_);
    crate::leanh::lean_closure_set(v___f_1961_, 7, v_inst_1952_);
    crate::leanh::lean_closure_set(v___f_1961_, 8, v_inst_1951_);
    crate::leanh::lean_closure_set(v___f_1961_, 9, v_inst_1950_);
    crate::leanh::lean_closure_set(v___f_1961_, 10, v_idStx_1955_);
    crate::leanh::lean_closure_set(v___f_1961_, 11, v_toBind_1957_);
    crate::leanh::lean_closure_set(v___f_1961_, 12, v_toApplicative_1956_);
    v___x_1962_ = crate::leanh::lean_apply_4(
        v_toBind_1957_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1958_,
        v___f_1961_,
    );
    return v___x_1962_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId(
    mut v_m_1963_: *mut crate::leanh::LeanObject,
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_inst_1966_: *mut crate::leanh::LeanObject,
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
    mut v_inst_1969_: *mut crate::leanh::LeanObject,
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_ns_1973_: *mut crate::leanh::LeanObject,
    mut v_idStx_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_Elab_OpenDecl_resolveId___redArg(
        v_inst_1964_,
        v_inst_1965_,
        v_inst_1966_,
        v_inst_1967_,
        v_inst_1968_,
        v_inst_1969_,
        v_inst_1970_,
        v_inst_1971_,
        v_inst_1972_,
        v_ns_1973_,
        v_idStx_1974_,
    );
    return v___x_1975_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0(
    mut v_decl_1976_: *mut crate::leanh::LeanObject,
    mut v_s_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_openDecls_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_openDecls_1978_ = crate::leanh::lean_ctor_get(v_s_1977_, 0);
                v_currNamespace_1979_ = crate::leanh::lean_ctor_get(v_s_1977_, 1);
                v_isSharedCheck_1989_ = (!crate::leanh::lean_is_exclusive(v_s_1977_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v___x_1981_ = v_s_1977_;
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_currNamespace_1979_);
                    crate::leanh::lean_inc(v_openDecls_1978_);
                    crate::leanh::lean_dec(v_s_1977_);
                    v___x_1981_ = crate::leanh::lean_box(0);
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1983_ = crate::leanh::lean_box(0);
                v___x_1984_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1984_, 0, v_decl_1976_);
                crate::leanh::lean_ctor_set(v___x_1984_, 1, v_openDecls_1978_);
                if v_isShared_1982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1981_, 0, v___x_1984_);
                    v___x_1986_ = v___x_1981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_currNamespace_1979_);
                    v___x_1986_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1983_);
                crate::leanh::lean_ctor_set(v___x_1987_, 1, v___x_1986_);
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
    mut v_inst_1990_: *mut crate::leanh::LeanObject,
    mut v_decl_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1993_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1993_, 0, v_decl_1991_);
    crate::leanh::lean_inc(v_a_1992_);
    v___x_1994_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_1994_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1994_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1994_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1994_, 3, v_a_1992_);
    crate::leanh::lean_closure_set(v___x_1994_, 4, v___f_1993_);
    v___x_1995_ = crate::leanh::lean_apply_2(v_inst_1990_, crate::leanh::lean_box(0), v___x_1994_);
    return v___x_1995_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(
    mut v_inst_1996_: *mut crate::leanh::LeanObject,
    mut v_decl_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1999_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_1996_,
        v_decl_1997_,
        v_a_1998_,
    );
    crate::leanh::lean_dec(v_a_1998_);
    return v_res_1999_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
    mut v_m_2000_: *mut crate::leanh::LeanObject,
    mut v_inst_2001_: *mut crate::leanh::LeanObject,
    mut v_decl_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2001_,
        v_decl_2002_,
        v_a_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(
    mut v_m_2005_: *mut crate::leanh::LeanObject,
    mut v_inst_2006_: *mut crate::leanh::LeanObject,
    mut v_decl_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
        v_m_2005_,
        v_inst_2006_,
        v_decl_2007_,
        v_a_2008_,
    );
    crate::leanh::lean_dec(v_a_2008_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(
    mut v_x_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = crate::leanh::lean_box(0);
    v___x_2012_ = l_Lean_mkConst(v_x_2010_, v___x_2011_);
    return v___x_2012_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(
    mut v_toPure_2013_: *mut crate::leanh::LeanObject,
    mut v_p_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2015_ = crate::leanh::lean_ctor_get(v_p_2014_, 1);
                crate::leanh::lean_inc(v_snd_2015_);
                crate::leanh::lean_dec_ref(v_p_2014_);
                v_fst_2016_ = crate::leanh::lean_ctor_get(v_snd_2015_, 0);
                v_snd_2017_ = crate::leanh::lean_ctor_get(v_snd_2015_, 1);
                v_isSharedCheck_2026_ = (!crate::leanh::lean_is_exclusive(v_snd_2015_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_2019_ = v_snd_2015_;
                    v_isShared_2020_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2017_);
                    crate::leanh::lean_inc(v_fst_2016_);
                    crate::leanh::lean_dec(v_snd_2015_);
                    v___x_2019_ = crate::leanh::lean_box(0);
                    v_isShared_2020_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2020_ == 0 {
                    v___x_2022_ = v___x_2019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fst_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_snd_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
                v___x_2024_ = crate::leanh::lean_apply_2(
                    v_toPure_2013_,
                    crate::leanh::lean_box(0),
                    v___x_2023_,
                );
                return v___x_2024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(
    mut v_snd_2027_: *mut crate::leanh::LeanObject,
    mut v_fst_2028_: *mut crate::leanh::LeanObject,
    mut v_toPure_2029_: *mut crate::leanh::LeanObject,
    mut v_declName_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = lean_array_push(v_snd_2027_, v_declName_2030_);
    v___x_2032_ = crate::leanh::lean_box(0);
    v___x_2033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2033_, 0, v_fst_2028_);
    crate::leanh::lean_ctor_set(v___x_2033_, 1, v___x_2031_);
    v___x_2034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2034_, 0, v___x_2032_);
    crate::leanh::lean_ctor_set(v___x_2034_, 1, v___x_2033_);
    v___x_2035_ =
        crate::leanh::lean_apply_2(v_toPure_2029_, crate::leanh::lean_box(0), v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(
    mut v_fst_2036_: *mut crate::leanh::LeanObject,
    mut v_snd_2037_: *mut crate::leanh::LeanObject,
    mut v_toPure_2038_: *mut crate::leanh::LeanObject,
    mut v_ex_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = lean_array_push(v_fst_2036_, v_ex_2039_);
    v___x_2041_ = crate::leanh::lean_box(0);
    v___x_2042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2040_);
    crate::leanh::lean_ctor_set(v___x_2042_, 1, v_snd_2037_);
    v___x_2043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2041_);
    crate::leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ =
        crate::leanh::lean_apply_2(v_toPure_2038_, crate::leanh::lean_box(0), v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_toPure_2046_: *mut crate::leanh::LeanObject,
    mut v_inst_2047_: *mut crate::leanh::LeanObject,
    mut v_inst_2048_: *mut crate::leanh::LeanObject,
    mut v_inst_2049_: *mut crate::leanh::LeanObject,
    mut v_inst_2050_: *mut crate::leanh::LeanObject,
    mut v_inst_2051_: *mut crate::leanh::LeanObject,
    mut v_inst_2052_: *mut crate::leanh::LeanObject,
    mut v_inst_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_idStx_2055_: *mut crate::leanh::LeanObject,
    mut v_toBind_2056_: *mut crate::leanh::LeanObject,
    mut v___f_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_x_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2061_ = crate::leanh::lean_ctor_get(v___y_2060_, 0);
    crate::leanh::lean_inc_n(v_fst_2061_, 2);
    v_snd_2062_ = crate::leanh::lean_ctor_get(v___y_2060_, 1);
    crate::leanh::lean_inc_n(v_snd_2062_, 2);
    crate::leanh::lean_dec_ref(v___y_2060_);
    v_tryCatch_2063_ = crate::leanh::lean_ctor_get(v_inst_2045_, 1);
    crate::leanh::lean_inc(v_tryCatch_2063_);
    crate::leanh::lean_inc(v_toPure_2046_);
    v___f_2064_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2064_, 0, v_snd_2062_);
    crate::leanh::lean_closure_set(v___f_2064_, 1, v_fst_2061_);
    crate::leanh::lean_closure_set(v___f_2064_, 2, v_toPure_2046_);
    v___f_2065_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2065_, 0, v_fst_2061_);
    crate::leanh::lean_closure_set(v___f_2065_, 1, v_snd_2062_);
    crate::leanh::lean_closure_set(v___f_2065_, 2, v_toPure_2046_);
    v___x_2066_ = l_Lean_Elab_OpenDecl_resolveId___redArg(
        v_inst_2047_,
        v_inst_2048_,
        v_inst_2045_,
        v_inst_2049_,
        v_inst_2050_,
        v_inst_2051_,
        v_inst_2052_,
        v_inst_2053_,
        v_inst_2054_,
        v_a_2058_,
        v_idStx_2055_,
    );
    crate::leanh::lean_inc(v_toBind_2056_);
    v___x_2067_ = crate::leanh::lean_apply_4(
        v_toBind_2056_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2066_,
        v___f_2064_,
    );
    v___x_2068_ = crate::leanh::lean_apply_3(
        v_tryCatch_2063_,
        crate::leanh::lean_box(0),
        v___x_2067_,
        v___f_2065_,
    );
    v___x_2069_ = crate::leanh::lean_apply_4(
        v_toBind_2056_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2068_,
        v___f_2057_,
    );
    return v___x_2069_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10;
    v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12;
    v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(
    mut v_snd_2096_: *mut crate::leanh::LeanObject,
    mut v_inst_2097_: *mut crate::leanh::LeanObject,
    mut v_inst_2098_: *mut crate::leanh::LeanObject,
    mut v_inst_2099_: *mut crate::leanh::LeanObject,
    mut v_idStx_2100_: *mut crate::leanh::LeanObject,
    mut v___f_2101_: *mut crate::leanh::LeanObject,
    mut v_inst_2102_: *mut crate::leanh::LeanObject,
    mut v_toBind_2103_: *mut crate::leanh::LeanObject,
    mut v___x_2104_: *mut crate::leanh::LeanObject,
    mut v_toPure_2105_: *mut crate::leanh::LeanObject,
    mut v_____r_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_sz_2117_: usize = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2107_ = lean_array_get_size(v_snd_2096_);
                v___x_2108_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_dec_eq(v___x_2107_, v___x_2108_);
                if v___x_2109_ == 0 {
                    crate::leanh::lean_dec(v_toPure_2105_);
                    crate::leanh::lean_inc_ref(v_inst_2098_);
                    v___x_2110_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2110_, 0, v_inst_2097_);
                    crate::leanh::lean_ctor_set(v___x_2110_, 1, v_inst_2098_);
                    crate::leanh::lean_ctor_set(v___x_2110_, 2, v_inst_2099_);
                    v___x_2111_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_getRef_2112_ = crate::leanh::lean_ctor_get(v_inst_2098_, 0);
                    v_withRef_2113_ = crate::leanh::lean_ctor_get(v_inst_2098_, 1);
                    v_isSharedCheck_2137_ = (!crate::leanh::lean_is_exclusive(v_inst_2098_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2115_ = v_inst_2098_;
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_withRef_2113_);
                        crate::leanh::lean_inc(v_getRef_2112_);
                        crate::leanh::lean_dec(v_inst_2098_);
                        v___x_2115_ = crate::leanh::lean_box(0);
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_toBind_2103_);
                    crate::leanh::lean_dec_ref(v_inst_2102_);
                    crate::leanh::lean_dec_ref(v___f_2101_);
                    crate::leanh::lean_dec(v_idStx_2100_);
                    crate::leanh::lean_dec(v_inst_2099_);
                    crate::leanh::lean_dec_ref(v_inst_2098_);
                    crate::leanh::lean_dec_ref(v_inst_2097_);
                    v___x_2138_ = lean_array_fget(v_snd_2096_, v___x_2104_);
                    crate::leanh::lean_dec(v_snd_2096_);
                    v___x_2139_ = crate::leanh::lean_apply_2(
                        v_toPure_2105_,
                        crate::leanh::lean_box(0),
                        v___x_2138_,
                    );
                    return v___x_2139_;
                }
            }
            1 => {
                v_sz_2117_ = lean_array_size(v_snd_2096_);
                v___x_2118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
                v___x_2119_ = l_Lean_Syntax_getId(v_idStx_2100_);
                v___x_2120_ = l_Lean_MessageData_ofName(v___x_2119_);
                if v_isShared_2116_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2115_, 7);
                    crate::leanh::lean_ctor_set(v___x_2115_, 1, v___x_2120_);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___x_2118_);
                    v___x_2122_ = v___x_2115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2123_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
                v___x_2124_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2124_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2124_, 1, v___x_2123_);
                v___x_2125_ = 0usize;
                v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2111_,
                    v___f_2101_,
                    v_sz_2117_,
                    v___x_2125_,
                    v_snd_2096_,
                );
                v___x_2127_ = lean_array_to_list(v___x_2126_);
                v___x_2128_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14;
                v___x_2129_ = crate::leanh::lean_box(0);
                v___x_2130_ = l_List_mapTR_loop___redArg(v___x_2128_, v___x_2127_, v___x_2129_);
                v___x_2131_ = l_Lean_MessageData_ofList(v___x_2130_);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2124_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                v___x_2133_ = l_Lean_throwError___redArg(v_inst_2102_, v___x_2110_, v___x_2132_);
                v___f_2134_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2134_, 0, v_idStx_2100_);
                crate::leanh::lean_closure_set(v___f_2134_, 1, v_withRef_2113_);
                crate::leanh::lean_closure_set(v___f_2134_, 2, v___x_2133_);
                v___x_2135_ = crate::leanh::lean_apply_4(
                    v_toBind_2103_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_2112_,
                    v___f_2134_,
                );
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(
    mut v_snd_2140_: *mut crate::leanh::LeanObject,
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_idStx_2144_: *mut crate::leanh::LeanObject,
    mut v___f_2145_: *mut crate::leanh::LeanObject,
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_toBind_2147_: *mut crate::leanh::LeanObject,
    mut v___x_2148_: *mut crate::leanh::LeanObject,
    mut v_toPure_2149_: *mut crate::leanh::LeanObject,
    mut v_____r_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(
        v_snd_2140_,
        v_inst_2141_,
        v_inst_2142_,
        v_inst_2143_,
        v_idStx_2144_,
        v___f_2145_,
        v_inst_2146_,
        v_toBind_2147_,
        v___x_2148_,
        v_toPure_2149_,
        v_____r_2150_,
    );
    crate::leanh::lean_dec(v___x_2148_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(
    mut v___f_2152_: *mut crate::leanh::LeanObject,
    mut v_____r_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2154_ = crate::leanh::lean_apply_1(v___f_2152_, v_____r_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
    mut v_idStx_2155_: *mut crate::leanh::LeanObject,
    mut v_withRef_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v_oldRef_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2159_ = l_Lean_replaceRef(v_idStx_2155_, v_oldRef_2158_);
    v___x_2160_ = crate::leanh::lean_apply_3(
        v_withRef_2156_,
        crate::leanh::lean_box(0),
        v_ref_2159_,
        v___y_2157_,
    );
    return v___x_2160_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(
    mut v_idStx_2161_: *mut crate::leanh::LeanObject,
    mut v_withRef_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v_oldRef_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
        v_idStx_2161_,
        v_withRef_2162_,
        v___y_2163_,
        v_oldRef_2164_,
    );
    crate::leanh::lean_dec(v_oldRef_2164_);
    crate::leanh::lean_dec(v_idStx_2161_);
    return v_res_2165_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1;
    v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
    mut v_inst_2173_: *mut crate::leanh::LeanObject,
    mut v_idStx_2174_: *mut crate::leanh::LeanObject,
    mut v___f_2175_: *mut crate::leanh::LeanObject,
    mut v_inst_2176_: *mut crate::leanh::LeanObject,
    mut v_toBind_2177_: *mut crate::leanh::LeanObject,
    mut v___x_2178_: *mut crate::leanh::LeanObject,
    mut v_toPure_2179_: *mut crate::leanh::LeanObject,
    mut v_nss_2180_: *mut crate::leanh::LeanObject,
    mut v_inst_2181_: *mut crate::leanh::LeanObject,
    mut v_____s_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2183_ = crate::leanh::lean_ctor_get(v_____s_2182_, 0);
                crate::leanh::lean_inc(v_fst_2183_);
                v_snd_2184_ = crate::leanh::lean_ctor_get(v_____s_2182_, 1);
                crate::leanh::lean_inc_n(v_snd_2184_, 2);
                crate::leanh::lean_dec_ref(v_____s_2182_);
                crate::leanh::lean_inc(v_toPure_2179_);
                crate::leanh::lean_inc(v___x_2178_);
                crate::leanh::lean_inc(v_toBind_2177_);
                crate::leanh::lean_inc_ref(v_inst_2176_);
                crate::leanh::lean_inc_ref(v___f_2175_);
                crate::leanh::lean_inc(v_idStx_2174_);
                crate::leanh::lean_inc(v_inst_2173_);
                crate::leanh::lean_inc_ref(v_inst_2172_);
                crate::leanh::lean_inc_ref(v_inst_2171_);
                v___f_2185_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    11,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_2185_, 0, v_snd_2184_);
                crate::leanh::lean_closure_set(v___f_2185_, 1, v_inst_2171_);
                crate::leanh::lean_closure_set(v___f_2185_, 2, v_inst_2172_);
                crate::leanh::lean_closure_set(v___f_2185_, 3, v_inst_2173_);
                crate::leanh::lean_closure_set(v___f_2185_, 4, v_idStx_2174_);
                crate::leanh::lean_closure_set(v___f_2185_, 5, v___f_2175_);
                crate::leanh::lean_closure_set(v___f_2185_, 6, v_inst_2176_);
                crate::leanh::lean_closure_set(v___f_2185_, 7, v_toBind_2177_);
                crate::leanh::lean_closure_set(v___f_2185_, 8, v___x_2178_);
                crate::leanh::lean_closure_set(v___f_2185_, 9, v_toPure_2179_);
                v___x_2186_ = lean_array_get_size(v_fst_2183_);
                v___x_2187_ = l_List_lengthTR___redArg(v_nss_2180_);
                v___x_2188_ = lean_nat_dec_eq(v___x_2186_, v___x_2187_);
                crate::leanh::lean_dec(v___x_2187_);
                if v___x_2188_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_2185_);
                    crate::leanh::lean_dec(v_fst_2183_);
                    crate::leanh::lean_dec_ref(v_inst_2181_);
                    v___x_2189_ = crate::leanh::lean_box(0);
                    v___x_2190_ =
                        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(
                            v_snd_2184_,
                            v_inst_2171_,
                            v_inst_2172_,
                            v_inst_2173_,
                            v_idStx_2174_,
                            v___f_2175_,
                            v_inst_2176_,
                            v_toBind_2177_,
                            v___x_2178_,
                            v_toPure_2179_,
                            v___x_2189_,
                        );
                    crate::leanh::lean_dec(v___x_2178_);
                    return v___x_2190_;
                } else {
                    crate::leanh::lean_dec(v_snd_2184_);
                    crate::leanh::lean_dec(v_toPure_2179_);
                    crate::leanh::lean_dec_ref(v___f_2175_);
                    v___f_2191_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2191_, 0, v___f_2185_);
                    v___x_2199_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2200_ = lean_nat_dec_eq(v___x_2186_, v___x_2199_);
                    if v___x_2200_ == 0 {
                        crate::leanh::lean_dec(v___x_2178_);
                        crate::leanh::lean_inc_ref(v_inst_2172_);
                        v___x_2201_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2201_, 0, v_inst_2171_);
                        crate::leanh::lean_ctor_set(v___x_2201_, 1, v_inst_2172_);
                        crate::leanh::lean_ctor_set(v___x_2201_, 2, v_inst_2173_);
                        v___x_2202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
                        v___x_2203_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(
                            v___x_2201_,
                            v_inst_2176_,
                            v_inst_2181_,
                            v___x_2202_,
                            v_fst_2183_,
                        );
                        v___y_2193_ = v___x_2203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2181_);
                        crate::leanh::lean_dec_ref(v_inst_2176_);
                        crate::leanh::lean_dec(v_inst_2173_);
                        v_throw_2204_ = crate::leanh::lean_ctor_get(v_inst_2171_, 0);
                        crate::leanh::lean_inc(v_throw_2204_);
                        crate::leanh::lean_dec_ref(v_inst_2171_);
                        v___x_2205_ = lean_array_fget(v_fst_2183_, v___x_2178_);
                        crate::leanh::lean_dec(v___x_2178_);
                        crate::leanh::lean_dec(v_fst_2183_);
                        v___x_2206_ = crate::leanh::lean_apply_2(
                            v_throw_2204_,
                            crate::leanh::lean_box(0),
                            v___x_2205_,
                        );
                        v___y_2193_ = v___x_2206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_getRef_2194_ = crate::leanh::lean_ctor_get(v_inst_2172_, 0);
                crate::leanh::lean_inc(v_getRef_2194_);
                v_withRef_2195_ = crate::leanh::lean_ctor_get(v_inst_2172_, 1);
                crate::leanh::lean_inc(v_withRef_2195_);
                crate::leanh::lean_dec_ref(v_inst_2172_);
                v___f_2196_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2196_, 0, v_idStx_2174_);
                crate::leanh::lean_closure_set(v___f_2196_, 1, v_withRef_2195_);
                crate::leanh::lean_closure_set(v___f_2196_, 2, v___y_2193_);
                crate::leanh::lean_inc(v_toBind_2177_);
                v___x_2197_ = crate::leanh::lean_apply_4(
                    v_toBind_2177_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_2194_,
                    v___f_2196_,
                );
                v___x_2198_ = crate::leanh::lean_apply_4(
                    v_toBind_2177_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2197_,
                    v___f_2191_,
                );
                return v___x_2198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed(
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_inst_2209_: *mut crate::leanh::LeanObject,
    mut v_idStx_2210_: *mut crate::leanh::LeanObject,
    mut v___f_2211_: *mut crate::leanh::LeanObject,
    mut v_inst_2212_: *mut crate::leanh::LeanObject,
    mut v_toBind_2213_: *mut crate::leanh::LeanObject,
    mut v___x_2214_: *mut crate::leanh::LeanObject,
    mut v_toPure_2215_: *mut crate::leanh::LeanObject,
    mut v_nss_2216_: *mut crate::leanh::LeanObject,
    mut v_inst_2217_: *mut crate::leanh::LeanObject,
    mut v_____s_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(
        v_inst_2207_,
        v_inst_2208_,
        v_inst_2209_,
        v_idStx_2210_,
        v___f_2211_,
        v_inst_2212_,
        v_toBind_2213_,
        v___x_2214_,
        v_toPure_2215_,
        v_nss_2216_,
        v_inst_2217_,
        v_____s_2218_,
    );
    crate::leanh::lean_dec(v_nss_2216_);
    return v_res_2219_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
    mut v_inst_2225_: *mut crate::leanh::LeanObject,
    mut v_inst_2226_: *mut crate::leanh::LeanObject,
    mut v_inst_2227_: *mut crate::leanh::LeanObject,
    mut v_inst_2228_: *mut crate::leanh::LeanObject,
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_inst_2230_: *mut crate::leanh::LeanObject,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
    mut v_inst_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_nss_2234_: *mut crate::leanh::LeanObject,
    mut v_idStx_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2236_ = crate::leanh::lean_ctor_get(v_inst_2225_, 0);
    v_toBind_2237_ = crate::leanh::lean_ctor_get(v_inst_2225_, 1);
    crate::leanh::lean_inc_n(v_toBind_2237_, 3);
    v_toPure_2238_ = crate::leanh::lean_ctor_get(v_toApplicative_2236_, 1);
    v___f_2239_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0;
    v___x_2240_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2241_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2;
    crate::leanh::lean_inc_n(v_toPure_2238_, 3);
    v___f_2242_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2242_, 0, v_toPure_2238_);
    crate::leanh::lean_inc(v_idStx_2235_);
    crate::leanh::lean_inc_ref(v_inst_2231_);
    crate::leanh::lean_inc(v_inst_2229_);
    crate::leanh::lean_inc_ref(v_inst_2228_);
    crate::leanh::lean_inc_ref_n(v_inst_2225_, 2);
    crate::leanh::lean_inc_ref(v_inst_2227_);
    v___f_2243_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4
            as *mut core::ffi::c_void,
        16,
        13,
    );
    crate::leanh::lean_closure_set(v___f_2243_, 0, v_inst_2227_);
    crate::leanh::lean_closure_set(v___f_2243_, 1, v_toPure_2238_);
    crate::leanh::lean_closure_set(v___f_2243_, 2, v_inst_2225_);
    crate::leanh::lean_closure_set(v___f_2243_, 3, v_inst_2226_);
    crate::leanh::lean_closure_set(v___f_2243_, 4, v_inst_2228_);
    crate::leanh::lean_closure_set(v___f_2243_, 5, v_inst_2229_);
    crate::leanh::lean_closure_set(v___f_2243_, 6, v_inst_2230_);
    crate::leanh::lean_closure_set(v___f_2243_, 7, v_inst_2231_);
    crate::leanh::lean_closure_set(v___f_2243_, 8, v_inst_2232_);
    crate::leanh::lean_closure_set(v___f_2243_, 9, v_inst_2233_);
    crate::leanh::lean_closure_set(v___f_2243_, 10, v_idStx_2235_);
    crate::leanh::lean_closure_set(v___f_2243_, 11, v_toBind_2237_);
    crate::leanh::lean_closure_set(v___f_2243_, 12, v___f_2242_);
    crate::leanh::lean_inc(v_nss_2234_);
    v___f_2244_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2244_, 0, v_inst_2227_);
    crate::leanh::lean_closure_set(v___f_2244_, 1, v_inst_2228_);
    crate::leanh::lean_closure_set(v___f_2244_, 2, v_inst_2229_);
    crate::leanh::lean_closure_set(v___f_2244_, 3, v_idStx_2235_);
    crate::leanh::lean_closure_set(v___f_2244_, 4, v___f_2239_);
    crate::leanh::lean_closure_set(v___f_2244_, 5, v_inst_2225_);
    crate::leanh::lean_closure_set(v___f_2244_, 6, v_toBind_2237_);
    crate::leanh::lean_closure_set(v___f_2244_, 7, v___x_2240_);
    crate::leanh::lean_closure_set(v___f_2244_, 8, v_toPure_2238_);
    crate::leanh::lean_closure_set(v___f_2244_, 9, v_nss_2234_);
    crate::leanh::lean_closure_set(v___f_2244_, 10, v_inst_2231_);
    v___x_2245_ =
        l_List_forIn_x27_loop___redArg(v_inst_2225_, v___f_2243_, v_nss_2234_, v___x_2241_);
    crate::leanh::lean_dec(v_nss_2234_);
    v___x_2246_ = crate::leanh::lean_apply_4(
        v_toBind_2237_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2245_,
        v___f_2244_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(
    mut v_m_2247_: *mut crate::leanh::LeanObject,
    mut v_inst_2248_: *mut crate::leanh::LeanObject,
    mut v_inst_2249_: *mut crate::leanh::LeanObject,
    mut v_inst_2250_: *mut crate::leanh::LeanObject,
    mut v_inst_2251_: *mut crate::leanh::LeanObject,
    mut v_inst_2252_: *mut crate::leanh::LeanObject,
    mut v_inst_2253_: *mut crate::leanh::LeanObject,
    mut v_inst_2254_: *mut crate::leanh::LeanObject,
    mut v_inst_2255_: *mut crate::leanh::LeanObject,
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
    mut v_nss_2257_: *mut crate::leanh::LeanObject,
    mut v_idStx_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
        v_inst_2248_,
        v_inst_2249_,
        v_inst_2250_,
        v_inst_2251_,
        v_inst_2252_,
        v_inst_2253_,
        v_inst_2254_,
        v_inst_2255_,
        v_inst_2256_,
        v_nss_2257_,
        v_idStx_2258_,
    );
    return v___x_2259_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0(
    mut v_toApplicative_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_openDecls_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_openDecls_2262_ = crate::leanh::lean_ctor_get(v_a_2261_, 0);
    crate::leanh::lean_inc(v_openDecls_2262_);
    crate::leanh::lean_dec_ref(v_a_2261_);
    v_toPure_2263_ = crate::leanh::lean_ctor_get(v_toApplicative_2260_, 1);
    crate::leanh::lean_inc(v_toPure_2263_);
    crate::leanh::lean_dec_ref(v_toApplicative_2260_);
    v___x_2264_ =
        crate::leanh::lean_apply_2(v_toPure_2263_, crate::leanh::lean_box(0), v_openDecls_2262_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
    mut v_inst_2265_: *mut crate::leanh::LeanObject,
    mut v_toBind_2266_: *mut crate::leanh::LeanObject,
    mut v___f_2267_: *mut crate::leanh::LeanObject,
    mut v_____r_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2269_);
    v___x_2270_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_2270_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2270_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2270_, 2, v___y_2269_);
    v___x_2271_ = crate::leanh::lean_apply_2(v_inst_2265_, crate::leanh::lean_box(0), v___x_2270_);
    v___x_2272_ = crate::leanh::lean_apply_4(
        v_toBind_2266_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2271_,
        v___f_2267_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_toBind_2274_: *mut crate::leanh::LeanObject,
    mut v___f_2275_: *mut crate::leanh::LeanObject,
    mut v_____r_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
        v_inst_2273_,
        v_toBind_2274_,
        v___f_2275_,
        v_____r_2276_,
        v___y_2277_,
    );
    crate::leanh::lean_dec(v___y_2277_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(
    mut v_x_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_2280_ = crate::leanh::lean_ctor_get(v_x_2279_, 1);
    crate::leanh::lean_inc(v_snd_2280_);
    return v_snd_2280_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(
    mut v_x_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_2281_);
    crate::leanh::lean_dec_ref(v_x_2281_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(
    mut v_x_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2284_ = crate::leanh::lean_ctor_get(v_x_2283_, 0);
    crate::leanh::lean_inc(v_fst_2284_);
    return v_fst_2284_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(
    mut v_x_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_2285_);
    crate::leanh::lean_dec_ref(v_x_2285_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_toPure_2288_: *mut crate::leanh::LeanObject,
    mut v_s_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2290_, 0, v_a_2287_);
    crate::leanh::lean_ctor_set(v___x_2290_, 1, v_s_2289_);
    v___x_2291_ =
        crate::leanh::lean_apply_2(v_toPure_2288_, crate::leanh::lean_box(0), v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(
    mut v_toPure_2292_: *mut crate::leanh::LeanObject,
    mut v_ref_2293_: *mut crate::leanh::LeanObject,
    mut v_inst_2294_: *mut crate::leanh::LeanObject,
    mut v_toBind_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2297_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2297_, 0, v_a_2296_);
    crate::leanh::lean_closure_set(v___f_2297_, 1, v_toPure_2292_);
    v___x_2298_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_2298_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2298_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2298_, 2, v_ref_2293_);
    v___x_2299_ = crate::leanh::lean_apply_2(v_inst_2294_, crate::leanh::lean_box(0), v___x_2298_);
    v___x_2300_ = crate::leanh::lean_apply_4(
        v_toBind_2295_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2299_,
        v___f_2297_,
    );
    return v___x_2300_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(
    mut v___f_2301_: *mut crate::leanh::LeanObject,
    mut v_ref_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = crate::leanh::lean_apply_2(v___f_2301_, v_a_2303_, v_ref_2302_);
    return v___x_2304_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(
    mut v___f_2305_: *mut crate::leanh::LeanObject,
    mut v_ref_2306_: *mut crate::leanh::LeanObject,
    mut v_a_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = crate::leanh::lean_box(0);
    v___x_2309_ = crate::leanh::lean_apply_2(v___f_2305_, v___x_2308_, v_ref_2306_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
    mut v___x_2311_: *mut crate::leanh::LeanObject,
    mut v___x_2312_: *mut crate::leanh::LeanObject,
    mut v___x_2313_: *mut crate::leanh::LeanObject,
    mut v___x_2314_: *mut crate::leanh::LeanObject,
    mut v___x_2315_: *mut crate::leanh::LeanObject,
    mut v_x_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    v___x_2317_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0;
    v___x_2318_ = l_Lean_Name_mkStr4(v___x_2311_, v___x_2312_, v___x_2313_, v___x_2317_);
    crate::leanh::lean_inc(v_x_2316_);
    v___x_2319_ = l_Lean_Syntax_isOfKind(v_x_2316_, v___x_2318_);
    crate::leanh::lean_dec(v___x_2318_);
    if v___x_2319_ == 0 {
        let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2316_);
        v___x_2320_ = crate::leanh::lean_box(0);
        return v___x_2320_;
    } else {
        let mut v_froms_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tos_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_froms_2321_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2314_);
        v_tos_2322_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2315_);
        crate::leanh::lean_dec(v_x_2316_);
        v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2323_, 0, v_froms_2321_);
        crate::leanh::lean_ctor_set(v___x_2323_, 1, v_tos_2322_);
        v___x_2324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(
    mut v___x_2325_: *mut crate::leanh::LeanObject,
    mut v___x_2326_: *mut crate::leanh::LeanObject,
    mut v___x_2327_: *mut crate::leanh::LeanObject,
    mut v___x_2328_: *mut crate::leanh::LeanObject,
    mut v___x_2329_: *mut crate::leanh::LeanObject,
    mut v_x_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
        v___x_2325_,
        v___x_2326_,
        v___x_2327_,
        v___x_2328_,
        v___x_2329_,
        v_x_2330_,
    );
    crate::leanh::lean_dec(v___x_2329_);
    crate::leanh::lean_dec(v___x_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(
    mut v___x_2332_: *mut crate::leanh::LeanObject,
    mut v_toPure_2333_: *mut crate::leanh::LeanObject,
    mut v_a_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2332_);
    v___x_2336_ =
        crate::leanh::lean_apply_2(v_toPure_2333_, crate::leanh::lean_box(0), v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
    mut v_snd_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
    mut v_toBind_2340_: *mut crate::leanh::LeanObject,
    mut v___f_2341_: *mut crate::leanh::LeanObject,
    mut v_____r_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Syntax_getId(v_snd_2337_);
    v___x_2345_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    crate::leanh::lean_ctor_set(v___x_2345_, 1, v_a_2338_);
    v___x_2346_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2339_,
        v___x_2345_,
        v___y_2343_,
    );
    v___x_2347_ = crate::leanh::lean_apply_4(
        v_toBind_2340_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2346_,
        v___f_2341_,
    );
    return v___x_2347_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(
    mut v_snd_2348_: *mut crate::leanh::LeanObject,
    mut v_a_2349_: *mut crate::leanh::LeanObject,
    mut v_inst_2350_: *mut crate::leanh::LeanObject,
    mut v_toBind_2351_: *mut crate::leanh::LeanObject,
    mut v___f_2352_: *mut crate::leanh::LeanObject,
    mut v_____r_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
        v_snd_2348_,
        v_a_2349_,
        v_inst_2350_,
        v_toBind_2351_,
        v___f_2352_,
        v_____r_2353_,
        v___y_2354_,
    );
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec(v_snd_2348_);
    return v_res_2355_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(
    mut v___f_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v_a_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2357_);
    v___x_2359_ = crate::leanh::lean_apply_2(v___f_2356_, v_a_2358_, v___y_2357_);
    return v___x_2359_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(
    mut v___f_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2363_ =
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v___f_2360_, v___y_2361_, v_a_2362_);
    crate::leanh::lean_dec(v___y_2361_);
    return v_res_2363_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(
    mut v___x_2364_: *mut crate::leanh::LeanObject,
    mut v___x_2365_: *mut crate::leanh::LeanObject,
    mut v___x_2366_: *mut crate::leanh::LeanObject,
    mut v___x_2367_: *mut crate::leanh::LeanObject,
    mut v_snd_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
    mut v___x_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v_toBind_2372_: *mut crate::leanh::LeanObject,
    mut v___f_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6682__overap_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6682__overap_2375_ = l_Lean_Elab_addConstInfo___redArg(
        v___x_2364_,
        v___x_2365_,
        v___x_2366_,
        v___x_2367_,
        v_snd_2368_,
        v_a_2369_,
        v___x_2370_,
    );
    crate::leanh::lean_inc(v___y_2371_);
    v___x_2376_ = crate::leanh::lean_apply_1(v___x_6682__overap_2375_, v___y_2371_);
    v___x_2377_ = crate::leanh::lean_apply_4(
        v_toBind_2372_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2376_,
        v___f_2373_,
    );
    return v___x_2377_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(
    mut v___x_2378_: *mut crate::leanh::LeanObject,
    mut v___x_2379_: *mut crate::leanh::LeanObject,
    mut v___x_2380_: *mut crate::leanh::LeanObject,
    mut v___x_2381_: *mut crate::leanh::LeanObject,
    mut v_snd_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v___x_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v_toBind_2386_: *mut crate::leanh::LeanObject,
    mut v___f_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(
        v___x_2378_,
        v___x_2379_,
        v___x_2380_,
        v___x_2381_,
        v_snd_2382_,
        v_a_2383_,
        v___x_2384_,
        v___y_2385_,
        v_toBind_2386_,
        v___f_2387_,
        v_a_2388_,
    );
    crate::leanh::lean_dec(v___y_2385_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(
    mut v___f_2390_: *mut crate::leanh::LeanObject,
    mut v___x_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___x_2393_: *mut crate::leanh::LeanObject,
    mut v___x_2394_: *mut crate::leanh::LeanObject,
    mut v___x_2395_: *mut crate::leanh::LeanObject,
    mut v___x_2396_: *mut crate::leanh::LeanObject,
    mut v_snd_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_toBind_2399_: *mut crate::leanh::LeanObject,
    mut v___f_2400_: *mut crate::leanh::LeanObject,
    mut v_fst_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enabled_2403_: u8 = 0;
    v_enabled_2403_ = crate::leanh::lean_ctor_get_uint8(
        v_a_2402_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2403_ == 0 {
        let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_2401_);
        crate::leanh::lean_dec(v___f_2400_);
        crate::leanh::lean_dec(v_toBind_2399_);
        crate::leanh::lean_dec(v_a_2398_);
        crate::leanh::lean_dec(v_snd_2397_);
        crate::leanh::lean_dec_ref(v___x_2396_);
        crate::leanh::lean_dec_ref(v___x_2395_);
        crate::leanh::lean_dec_ref(v___x_2394_);
        crate::leanh::lean_dec_ref(v___x_2393_);
        crate::leanh::lean_inc(v___y_2392_);
        v___x_2404_ = crate::leanh::lean_apply_2(v___f_2390_, v___x_2391_, v___y_2392_);
        return v___x_2404_;
    } else {
        let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6697__overap_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2390_);
        v___x_2405_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_toBind_2399_);
        crate::leanh::lean_inc_n(v___y_2392_, 2);
        crate::leanh::lean_inc(v_a_2398_);
        crate::leanh::lean_inc_ref(v___x_2396_);
        crate::leanh::lean_inc_ref(v___x_2395_);
        crate::leanh::lean_inc_ref(v___x_2394_);
        crate::leanh::lean_inc_ref(v___x_2393_);
        v___f_2406_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed as *mut core::ffi::c_void,
            11,
            10,
        );
        crate::leanh::lean_closure_set(v___f_2406_, 0, v___x_2393_);
        crate::leanh::lean_closure_set(v___f_2406_, 1, v___x_2394_);
        crate::leanh::lean_closure_set(v___f_2406_, 2, v___x_2395_);
        crate::leanh::lean_closure_set(v___f_2406_, 3, v___x_2396_);
        crate::leanh::lean_closure_set(v___f_2406_, 4, v_snd_2397_);
        crate::leanh::lean_closure_set(v___f_2406_, 5, v_a_2398_);
        crate::leanh::lean_closure_set(v___f_2406_, 6, v___x_2405_);
        crate::leanh::lean_closure_set(v___f_2406_, 7, v___y_2392_);
        crate::leanh::lean_closure_set(v___f_2406_, 8, v_toBind_2399_);
        crate::leanh::lean_closure_set(v___f_2406_, 9, v___f_2400_);
        v___x_6697__overap_2407_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2393_,
            v___x_2394_,
            v___x_2395_,
            v___x_2396_,
            v_fst_2401_,
            v_a_2398_,
            v___x_2405_,
        );
        v___x_2408_ = crate::leanh::lean_apply_1(v___x_6697__overap_2407_, v___y_2392_);
        v___x_2409_ = crate::leanh::lean_apply_4(
            v_toBind_2399_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2408_,
            v___f_2406_,
        );
        return v___x_2409_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(
    mut v___f_2410_: *mut crate::leanh::LeanObject,
    mut v___x_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___x_2413_: *mut crate::leanh::LeanObject,
    mut v___x_2414_: *mut crate::leanh::LeanObject,
    mut v___x_2415_: *mut crate::leanh::LeanObject,
    mut v___x_2416_: *mut crate::leanh::LeanObject,
    mut v_snd_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_toBind_2419_: *mut crate::leanh::LeanObject,
    mut v___f_2420_: *mut crate::leanh::LeanObject,
    mut v_fst_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(
        v___f_2410_,
        v___x_2411_,
        v___y_2412_,
        v___x_2413_,
        v___x_2414_,
        v___x_2415_,
        v___x_2416_,
        v_snd_2417_,
        v_a_2418_,
        v_toBind_2419_,
        v___f_2420_,
        v_fst_2421_,
        v_a_2422_,
    );
    crate::leanh::lean_dec_ref(v_a_2422_);
    crate::leanh::lean_dec(v___y_2412_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(
    mut v___x_2424_: *mut crate::leanh::LeanObject,
    mut v_inst_2425_: *mut crate::leanh::LeanObject,
    mut v_snd_2426_: *mut crate::leanh::LeanObject,
    mut v_inst_2427_: *mut crate::leanh::LeanObject,
    mut v_toBind_2428_: *mut crate::leanh::LeanObject,
    mut v___f_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___x_2431_: *mut crate::leanh::LeanObject,
    mut v___x_2432_: *mut crate::leanh::LeanObject,
    mut v___x_2433_: *mut crate::leanh::LeanObject,
    mut v___x_2434_: *mut crate::leanh::LeanObject,
    mut v_fst_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2425_);
    v___x_2437_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2424_, v_inst_2425_);
    v_getInfoState_2438_ = crate::leanh::lean_ctor_get(v_inst_2425_, 0);
    crate::leanh::lean_inc(v_getInfoState_2438_);
    crate::leanh::lean_dec_ref(v_inst_2425_);
    crate::leanh::lean_inc_n(v_toBind_2428_, 2);
    crate::leanh::lean_inc(v_a_2436_);
    crate::leanh::lean_inc(v_snd_2426_);
    v___f_2439_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2439_, 0, v_snd_2426_);
    crate::leanh::lean_closure_set(v___f_2439_, 1, v_a_2436_);
    crate::leanh::lean_closure_set(v___f_2439_, 2, v_inst_2427_);
    crate::leanh::lean_closure_set(v___f_2439_, 3, v_toBind_2428_);
    crate::leanh::lean_closure_set(v___f_2439_, 4, v___f_2429_);
    crate::leanh::lean_inc_n(v___y_2430_, 2);
    crate::leanh::lean_inc_ref(v___f_2439_);
    v___f_2440_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2440_, 0, v___f_2439_);
    crate::leanh::lean_closure_set(v___f_2440_, 1, v___y_2430_);
    v___f_2441_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_2441_, 0, v___f_2439_);
    crate::leanh::lean_closure_set(v___f_2441_, 1, v___x_2431_);
    crate::leanh::lean_closure_set(v___f_2441_, 2, v___y_2430_);
    crate::leanh::lean_closure_set(v___f_2441_, 3, v___x_2432_);
    crate::leanh::lean_closure_set(v___f_2441_, 4, v___x_2437_);
    crate::leanh::lean_closure_set(v___f_2441_, 5, v___x_2433_);
    crate::leanh::lean_closure_set(v___f_2441_, 6, v___x_2434_);
    crate::leanh::lean_closure_set(v___f_2441_, 7, v_snd_2426_);
    crate::leanh::lean_closure_set(v___f_2441_, 8, v_a_2436_);
    crate::leanh::lean_closure_set(v___f_2441_, 9, v_toBind_2428_);
    crate::leanh::lean_closure_set(v___f_2441_, 10, v___f_2440_);
    crate::leanh::lean_closure_set(v___f_2441_, 11, v_fst_2435_);
    v___x_2442_ = crate::leanh::lean_apply_4(
        v_toBind_2428_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInfoState_2438_,
        v___f_2441_,
    );
    return v___x_2442_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(
    mut v___x_2443_: *mut crate::leanh::LeanObject,
    mut v_inst_2444_: *mut crate::leanh::LeanObject,
    mut v_snd_2445_: *mut crate::leanh::LeanObject,
    mut v_inst_2446_: *mut crate::leanh::LeanObject,
    mut v_toBind_2447_: *mut crate::leanh::LeanObject,
    mut v___f_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___x_2450_: *mut crate::leanh::LeanObject,
    mut v___x_2451_: *mut crate::leanh::LeanObject,
    mut v___x_2452_: *mut crate::leanh::LeanObject,
    mut v___x_2453_: *mut crate::leanh::LeanObject,
    mut v_fst_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(
        v___x_2443_,
        v_inst_2444_,
        v_snd_2445_,
        v_inst_2446_,
        v_toBind_2447_,
        v___f_2448_,
        v___y_2449_,
        v___x_2450_,
        v___x_2451_,
        v___x_2452_,
        v___x_2453_,
        v_fst_2454_,
        v_a_2455_,
    );
    crate::leanh::lean_dec(v___y_2449_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(
    mut v___x_2457_: *mut crate::leanh::LeanObject,
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v_inst_2459_: *mut crate::leanh::LeanObject,
    mut v_toBind_2460_: *mut crate::leanh::LeanObject,
    mut v___f_2461_: *mut crate::leanh::LeanObject,
    mut v___x_2462_: *mut crate::leanh::LeanObject,
    mut v___x_2463_: *mut crate::leanh::LeanObject,
    mut v___x_2464_: *mut crate::leanh::LeanObject,
    mut v___x_2465_: *mut crate::leanh::LeanObject,
    mut v_inst_2466_: *mut crate::leanh::LeanObject,
    mut v_inst_2467_: *mut crate::leanh::LeanObject,
    mut v___x_2468_: *mut crate::leanh::LeanObject,
    mut v___x_2469_: *mut crate::leanh::LeanObject,
    mut v___x_2470_: *mut crate::leanh::LeanObject,
    mut v___f_2471_: *mut crate::leanh::LeanObject,
    mut v___x_2472_: *mut crate::leanh::LeanObject,
    mut v_a_2473_: *mut crate::leanh::LeanObject,
    mut v_a_2474_: *mut crate::leanh::LeanObject,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738__overap_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2478_ = crate::leanh::lean_ctor_get(v_a_2474_, 0);
    crate::leanh::lean_inc_n(v_fst_2478_, 2);
    v_snd_2479_ = crate::leanh::lean_ctor_get(v_a_2474_, 1);
    crate::leanh::lean_inc(v_snd_2479_);
    crate::leanh::lean_dec_ref(v_a_2474_);
    crate::leanh::lean_inc_ref(v___x_2464_);
    crate::leanh::lean_inc_ref(v___x_2463_);
    crate::leanh::lean_inc_n(v___y_2477_, 2);
    crate::leanh::lean_inc(v_toBind_2460_);
    crate::leanh::lean_inc(v___x_2457_);
    v___f_2480_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_2480_, 0, v___x_2457_);
    crate::leanh::lean_closure_set(v___f_2480_, 1, v_inst_2458_);
    crate::leanh::lean_closure_set(v___f_2480_, 2, v_snd_2479_);
    crate::leanh::lean_closure_set(v___f_2480_, 3, v_inst_2459_);
    crate::leanh::lean_closure_set(v___f_2480_, 4, v_toBind_2460_);
    crate::leanh::lean_closure_set(v___f_2480_, 5, v___f_2461_);
    crate::leanh::lean_closure_set(v___f_2480_, 6, v___y_2477_);
    crate::leanh::lean_closure_set(v___f_2480_, 7, v___x_2462_);
    crate::leanh::lean_closure_set(v___f_2480_, 8, v___x_2463_);
    crate::leanh::lean_closure_set(v___f_2480_, 9, v___x_2464_);
    crate::leanh::lean_closure_set(v___f_2480_, 10, v___x_2465_);
    crate::leanh::lean_closure_set(v___f_2480_, 11, v_fst_2478_);
    v___x_2481_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2457_, v_inst_2466_);
    v___x_2482_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_2482_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2482_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2482_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2482_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2482_, 4, v_inst_2467_);
    v___x_6738__overap_2483_ = l_Lean_Elab_OpenDecl_resolveId___redArg(
        v___x_2463_,
        v___x_2464_,
        v___x_2468_,
        v___x_2469_,
        v___x_2470_,
        v___f_2471_,
        v___x_2481_,
        v___x_2482_,
        v___x_2472_,
        v_a_2473_,
        v_fst_2478_,
    );
    v___x_2484_ = crate::leanh::lean_apply_1(v___x_6738__overap_2483_, v___y_2477_);
    v___x_2485_ = crate::leanh::lean_apply_4(
        v_toBind_2460_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2484_,
        v___f_2480_,
    );
    return v___x_2485_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_2487_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_2488_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toBind_2489_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_2490_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2491_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2492_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2493_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2494_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_2495_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2496_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2497_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2498_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2499_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2500_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2501_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_2502_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_2503_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x_2504_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2505_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2506_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(
        v___x_2486_,
        v_inst_2487_,
        v_inst_2488_,
        v_toBind_2489_,
        v___f_2490_,
        v___x_2491_,
        v___x_2492_,
        v___x_2493_,
        v___x_2494_,
        v_inst_2495_,
        v_inst_2496_,
        v___x_2497_,
        v___x_2498_,
        v___x_2499_,
        v___f_2500_,
        v___x_2501_,
        v_a_2502_,
        v_a_2503_,
        v_x_2504_,
        v___y_2505_,
        v___y_2506_,
    );
    crate::leanh::lean_dec(v___y_2506_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(
    mut v_froms_2508_: *mut crate::leanh::LeanObject,
    mut v_tos_2509_: *mut crate::leanh::LeanObject,
    mut v_toPure_2510_: *mut crate::leanh::LeanObject,
    mut v___x_2511_: *mut crate::leanh::LeanObject,
    mut v_inst_2512_: *mut crate::leanh::LeanObject,
    mut v_inst_2513_: *mut crate::leanh::LeanObject,
    mut v_toBind_2514_: *mut crate::leanh::LeanObject,
    mut v___x_2515_: *mut crate::leanh::LeanObject,
    mut v___x_2516_: *mut crate::leanh::LeanObject,
    mut v___x_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v___x_2520_: *mut crate::leanh::LeanObject,
    mut v___x_2521_: *mut crate::leanh::LeanObject,
    mut v___x_2522_: *mut crate::leanh::LeanObject,
    mut v___f_2523_: *mut crate::leanh::LeanObject,
    mut v___x_2524_: *mut crate::leanh::LeanObject,
    mut v___x_2525_: usize,
    mut v_ref_2526_: *mut crate::leanh::LeanObject,
    mut v___f_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2533_: usize = 0;
    let mut v___x_6759__overap_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Array_zip___redArg(v_froms_2508_, v_tos_2509_);
    v___x_2530_ = crate::leanh::lean_box(0);
    v___f_2531_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2531_, 0, v___x_2530_);
    crate::leanh::lean_closure_set(v___f_2531_, 1, v_toPure_2510_);
    crate::leanh::lean_inc_ref(v___x_2515_);
    crate::leanh::lean_inc(v_toBind_2514_);
    v___f_2532_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2532_, 0, v___x_2511_);
    crate::leanh::lean_closure_set(v___f_2532_, 1, v_inst_2512_);
    crate::leanh::lean_closure_set(v___f_2532_, 2, v_inst_2513_);
    crate::leanh::lean_closure_set(v___f_2532_, 3, v_toBind_2514_);
    crate::leanh::lean_closure_set(v___f_2532_, 4, v___f_2531_);
    crate::leanh::lean_closure_set(v___f_2532_, 5, v___x_2530_);
    crate::leanh::lean_closure_set(v___f_2532_, 6, v___x_2515_);
    crate::leanh::lean_closure_set(v___f_2532_, 7, v___x_2516_);
    crate::leanh::lean_closure_set(v___f_2532_, 8, v___x_2517_);
    crate::leanh::lean_closure_set(v___f_2532_, 9, v_inst_2518_);
    crate::leanh::lean_closure_set(v___f_2532_, 10, v_inst_2519_);
    crate::leanh::lean_closure_set(v___f_2532_, 11, v___x_2520_);
    crate::leanh::lean_closure_set(v___f_2532_, 12, v___x_2521_);
    crate::leanh::lean_closure_set(v___f_2532_, 13, v___x_2522_);
    crate::leanh::lean_closure_set(v___f_2532_, 14, v___f_2523_);
    crate::leanh::lean_closure_set(v___f_2532_, 15, v___x_2524_);
    crate::leanh::lean_closure_set(v___f_2532_, 16, v_a_2528_);
    v_sz_2533_ = lean_array_size(v___x_2529_);
    v___x_6759__overap_2534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2515_,
        v___x_2529_,
        v___f_2532_,
        v_sz_2533_,
        v___x_2525_,
        v___x_2530_,
    );
    v___x_2535_ = crate::leanh::lean_apply_1(v___x_6759__overap_2534_, v_ref_2526_);
    v___x_2536_ = crate::leanh::lean_apply_4(
        v_toBind_2514_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2535_,
        v___f_2527_,
    );
    return v___x_2536_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_froms_2537_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_tos_2538_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_toPure_2539_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2540_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_2541_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_2542_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2543_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2544_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2545_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2546_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2547_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_2548_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2549_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2550_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_2551_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___f_2552_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_2553_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_2554_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_ref_2555_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___f_2556_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_a_2557_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_7638__boxed_2558_: usize = 0;
    let mut v_res_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7638__boxed_2558_ = crate::leanh::lean_unbox_usize(v___x_2554_);
    crate::leanh::lean_dec(v___x_2554_);
    v_res_2559_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(
        v_froms_2537_,
        v_tos_2538_,
        v_toPure_2539_,
        v___x_2540_,
        v_inst_2541_,
        v_inst_2542_,
        v_toBind_2543_,
        v___x_2544_,
        v___x_2545_,
        v___x_2546_,
        v_inst_2547_,
        v_inst_2548_,
        v___x_2549_,
        v___x_2550_,
        v___x_2551_,
        v___f_2552_,
        v___x_2553_,
        v___x_7638__boxed_2558_,
        v_ref_2555_,
        v___f_2556_,
        v_a_2557_,
    );
    crate::leanh::lean_dec_ref(v_tos_2538_);
    crate::leanh::lean_dec_ref(v_froms_2537_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
    mut v___x_2560_: u8,
    mut v___x_2561_: u8,
    mut v_x1_2562_: *mut crate::leanh::LeanObject,
    mut v_x2_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v_snd_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v_unused_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_unused_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2564_ = crate::leanh::lean_ctor_get(v_x1_2562_, 0);
                v___x_2565_ = (crate::leanh::lean_unbox(v_fst_2564_) as u8);
                if v___x_2565_ == 0 {
                    crate::leanh::lean_dec(v_x2_2563_);
                    v_snd_2566_ = crate::leanh::lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2574_ = (!crate::leanh::lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2574_ == 0 {
                        v_unused_2575_ = crate::leanh::lean_ctor_get(v_x1_2562_, 0);
                        crate::leanh::lean_dec(v_unused_2575_);
                        v___x_2568_ = v_x1_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2566_);
                        crate::leanh::lean_dec(v_x1_2562_);
                        v___x_2568_ = crate::leanh::lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2576_ = crate::leanh::lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2585_ = (!crate::leanh::lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2585_ == 0 {
                        v_unused_2586_ = crate::leanh::lean_ctor_get(v_x1_2562_, 0);
                        crate::leanh::lean_dec(v_unused_2586_);
                        v___x_2578_ = v_x1_2562_;
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2576_);
                        crate::leanh::lean_dec(v_x1_2562_);
                        v___x_2578_ = crate::leanh::lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2570_ = crate::leanh::lean_box((v___x_2560_) as usize);
                if v_isShared_2569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2570_);
                    v___x_2572_ = v___x_2568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_snd_2566_);
                    v___x_2572_ = v_reuseFailAlloc_2573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2572_;
            }
            3 => {
                v___x_2580_ = lean_array_push(v_snd_2576_, v_x2_2563_);
                v___x_2581_ = crate::leanh::lean_box((v___x_2561_) as usize);
                if v_isShared_2579_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2578_, 1, v___x_2580_);
                    crate::leanh::lean_ctor_set(v___x_2578_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2580_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(
    mut v___x_2587_: *mut crate::leanh::LeanObject,
    mut v___x_2588_: *mut crate::leanh::LeanObject,
    mut v_x1_2589_: *mut crate::leanh::LeanObject,
    mut v_x2_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7682__boxed_2591_: u8 = 0;
    let mut v___x_7683__boxed_2592_: u8 = 0;
    let mut v_res_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7682__boxed_2591_ = (crate::leanh::lean_unbox(v___x_2587_) as u8);
    v___x_7683__boxed_2592_ = (crate::leanh::lean_unbox(v___x_2588_) as u8);
    v_res_2593_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
        v___x_7682__boxed_2591_,
        v___x_7683__boxed_2592_,
        v_x1_2589_,
        v_x2_2590_,
    );
    return v_res_2593_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(
    mut v_ids_2594_: *mut crate::leanh::LeanObject,
    mut v___f_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
    mut v_inst_2597_: *mut crate::leanh::LeanObject,
    mut v_ref_2598_: *mut crate::leanh::LeanObject,
    mut v_toBind_2599_: *mut crate::leanh::LeanObject,
    mut v___f_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
    v_sz_2603_ = lean_array_size(v_ids_2594_);
    v___x_2604_ = 0usize;
    v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2602_,
        v___f_2595_,
        v_sz_2603_,
        v___x_2604_,
        v_ids_2594_,
    );
    v___x_2606_ = lean_array_to_list(v___x_2605_);
    v___x_2607_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2607_, 0, v_a_2596_);
    crate::leanh::lean_ctor_set(v___x_2607_, 1, v___x_2606_);
    v___x_2608_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2597_,
        v___x_2607_,
        v_ref_2598_,
    );
    v___x_2609_ = crate::leanh::lean_apply_4(
        v_toBind_2599_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2608_,
        v___f_2600_,
    );
    return v___x_2609_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(
    mut v_ids_2610_: *mut crate::leanh::LeanObject,
    mut v___f_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_inst_2613_: *mut crate::leanh::LeanObject,
    mut v_ref_2614_: *mut crate::leanh::LeanObject,
    mut v_toBind_2615_: *mut crate::leanh::LeanObject,
    mut v___f_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2618_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(
        v_ids_2610_,
        v___f_2611_,
        v_a_2612_,
        v_inst_2613_,
        v_ref_2614_,
        v_toBind_2615_,
        v___f_2616_,
        v_a_2617_,
    );
    crate::leanh::lean_dec(v_ref_2614_);
    return v_res_2618_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(
    mut v___x_2619_: *mut crate::leanh::LeanObject,
    mut v_toPure_2620_: *mut crate::leanh::LeanObject,
    mut v___x_2621_: *mut crate::leanh::LeanObject,
    mut v___x_2622_: *mut crate::leanh::LeanObject,
    mut v___x_2623_: *mut crate::leanh::LeanObject,
    mut v___x_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v_toBind_2628_: *mut crate::leanh::LeanObject,
    mut v___f_2629_: *mut crate::leanh::LeanObject,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enabled_2631_: u8 = 0;
    v_enabled_2631_ = crate::leanh::lean_ctor_get_uint8(
        v_a_2630_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2631_ == 0 {
        let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2629_);
        crate::leanh::lean_dec(v_toBind_2628_);
        crate::leanh::lean_dec(v_a_2626_);
        crate::leanh::lean_dec(v_a_2625_);
        crate::leanh::lean_dec_ref(v___x_2624_);
        crate::leanh::lean_dec_ref(v___x_2623_);
        crate::leanh::lean_dec_ref(v___x_2622_);
        crate::leanh::lean_dec_ref(v___x_2621_);
        v___x_2632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2619_);
        v___x_2633_ =
            crate::leanh::lean_apply_2(v_toPure_2620_, crate::leanh::lean_box(0), v___x_2632_);
        return v___x_2633_;
    } else {
        let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6804__overap_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2620_);
        v___x_2634_ = crate::leanh::lean_box(0);
        v___x_6804__overap_2635_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2621_,
            v___x_2622_,
            v___x_2623_,
            v___x_2624_,
            v_a_2625_,
            v_a_2626_,
            v___x_2634_,
        );
        crate::leanh::lean_inc(v___y_2627_);
        v___x_2636_ = crate::leanh::lean_apply_1(v___x_6804__overap_2635_, v___y_2627_);
        v___x_2637_ = crate::leanh::lean_apply_4(
            v_toBind_2628_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2636_,
            v___f_2629_,
        );
        return v___x_2637_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(
    mut v___x_2638_: *mut crate::leanh::LeanObject,
    mut v_toPure_2639_: *mut crate::leanh::LeanObject,
    mut v___x_2640_: *mut crate::leanh::LeanObject,
    mut v___x_2641_: *mut crate::leanh::LeanObject,
    mut v___x_2642_: *mut crate::leanh::LeanObject,
    mut v___x_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v_toBind_2647_: *mut crate::leanh::LeanObject,
    mut v___f_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(
        v___x_2638_,
        v_toPure_2639_,
        v___x_2640_,
        v___x_2641_,
        v___x_2642_,
        v___x_2643_,
        v_a_2644_,
        v_a_2645_,
        v___y_2646_,
        v_toBind_2647_,
        v___f_2648_,
        v_a_2649_,
    );
    crate::leanh::lean_dec_ref(v_a_2649_);
    crate::leanh::lean_dec(v___y_2646_);
    return v_res_2650_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(
    mut v___x_2651_: *mut crate::leanh::LeanObject,
    mut v_inst_2652_: *mut crate::leanh::LeanObject,
    mut v___x_2653_: *mut crate::leanh::LeanObject,
    mut v_toPure_2654_: *mut crate::leanh::LeanObject,
    mut v___x_2655_: *mut crate::leanh::LeanObject,
    mut v___x_2656_: *mut crate::leanh::LeanObject,
    mut v___x_2657_: *mut crate::leanh::LeanObject,
    mut v_a_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v_toBind_2660_: *mut crate::leanh::LeanObject,
    mut v___f_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2652_);
    v___x_2663_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2651_, v_inst_2652_);
    v_getInfoState_2664_ = crate::leanh::lean_ctor_get(v_inst_2652_, 0);
    crate::leanh::lean_inc(v_getInfoState_2664_);
    crate::leanh::lean_dec_ref(v_inst_2652_);
    crate::leanh::lean_inc(v_toBind_2660_);
    crate::leanh::lean_inc(v___y_2659_);
    v___f_2665_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2665_, 0, v___x_2653_);
    crate::leanh::lean_closure_set(v___f_2665_, 1, v_toPure_2654_);
    crate::leanh::lean_closure_set(v___f_2665_, 2, v___x_2655_);
    crate::leanh::lean_closure_set(v___f_2665_, 3, v___x_2663_);
    crate::leanh::lean_closure_set(v___f_2665_, 4, v___x_2656_);
    crate::leanh::lean_closure_set(v___f_2665_, 5, v___x_2657_);
    crate::leanh::lean_closure_set(v___f_2665_, 6, v_a_2658_);
    crate::leanh::lean_closure_set(v___f_2665_, 7, v_a_2662_);
    crate::leanh::lean_closure_set(v___f_2665_, 8, v___y_2659_);
    crate::leanh::lean_closure_set(v___f_2665_, 9, v_toBind_2660_);
    crate::leanh::lean_closure_set(v___f_2665_, 10, v___f_2661_);
    v___x_2666_ = crate::leanh::lean_apply_4(
        v_toBind_2660_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInfoState_2664_,
        v___f_2665_,
    );
    return v___x_2666_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(
    mut v___x_2667_: *mut crate::leanh::LeanObject,
    mut v_inst_2668_: *mut crate::leanh::LeanObject,
    mut v___x_2669_: *mut crate::leanh::LeanObject,
    mut v_toPure_2670_: *mut crate::leanh::LeanObject,
    mut v___x_2671_: *mut crate::leanh::LeanObject,
    mut v___x_2672_: *mut crate::leanh::LeanObject,
    mut v___x_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v_toBind_2676_: *mut crate::leanh::LeanObject,
    mut v___f_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(
        v___x_2667_,
        v_inst_2668_,
        v___x_2669_,
        v_toPure_2670_,
        v___x_2671_,
        v___x_2672_,
        v___x_2673_,
        v_a_2674_,
        v___y_2675_,
        v_toBind_2676_,
        v___f_2677_,
        v_a_2678_,
    );
    crate::leanh::lean_dec(v___y_2675_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(
    mut v___x_2680_: *mut crate::leanh::LeanObject,
    mut v_inst_2681_: *mut crate::leanh::LeanObject,
    mut v___x_2682_: *mut crate::leanh::LeanObject,
    mut v_toPure_2683_: *mut crate::leanh::LeanObject,
    mut v___x_2684_: *mut crate::leanh::LeanObject,
    mut v___x_2685_: *mut crate::leanh::LeanObject,
    mut v___x_2686_: *mut crate::leanh::LeanObject,
    mut v_toBind_2687_: *mut crate::leanh::LeanObject,
    mut v___f_2688_: *mut crate::leanh::LeanObject,
    mut v_inst_2689_: *mut crate::leanh::LeanObject,
    mut v_inst_2690_: *mut crate::leanh::LeanObject,
    mut v___x_2691_: *mut crate::leanh::LeanObject,
    mut v___x_2692_: *mut crate::leanh::LeanObject,
    mut v___x_2693_: *mut crate::leanh::LeanObject,
    mut v___f_2694_: *mut crate::leanh::LeanObject,
    mut v___x_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_x_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837__overap_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2687_);
    crate::leanh::lean_inc_n(v___y_2700_, 2);
    crate::leanh::lean_inc(v_a_2697_);
    crate::leanh::lean_inc_ref(v___x_2685_);
    crate::leanh::lean_inc_ref(v___x_2684_);
    crate::leanh::lean_inc(v___x_2680_);
    v___f_2701_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2701_, 0, v___x_2680_);
    crate::leanh::lean_closure_set(v___f_2701_, 1, v_inst_2681_);
    crate::leanh::lean_closure_set(v___f_2701_, 2, v___x_2682_);
    crate::leanh::lean_closure_set(v___f_2701_, 3, v_toPure_2683_);
    crate::leanh::lean_closure_set(v___f_2701_, 4, v___x_2684_);
    crate::leanh::lean_closure_set(v___f_2701_, 5, v___x_2685_);
    crate::leanh::lean_closure_set(v___f_2701_, 6, v___x_2686_);
    crate::leanh::lean_closure_set(v___f_2701_, 7, v_a_2697_);
    crate::leanh::lean_closure_set(v___f_2701_, 8, v___y_2700_);
    crate::leanh::lean_closure_set(v___f_2701_, 9, v_toBind_2687_);
    crate::leanh::lean_closure_set(v___f_2701_, 10, v___f_2688_);
    v___x_2702_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2680_, v_inst_2689_);
    v___x_2703_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_2703_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2703_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2703_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2703_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2703_, 4, v_inst_2690_);
    v___x_6837__overap_2704_ = l_Lean_Elab_OpenDecl_resolveId___redArg(
        v___x_2684_,
        v___x_2685_,
        v___x_2691_,
        v___x_2692_,
        v___x_2693_,
        v___f_2694_,
        v___x_2702_,
        v___x_2703_,
        v___x_2695_,
        v_a_2696_,
        v_a_2697_,
    );
    v___x_2705_ = crate::leanh::lean_apply_1(v___x_6837__overap_2704_, v___y_2700_);
    v___x_2706_ = crate::leanh::lean_apply_4(
        v_toBind_2687_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2705_,
        v___f_2701_,
    );
    return v___x_2706_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_2708_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2709_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toPure_2710_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2711_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2712_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2713_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toBind_2714_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_2715_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_2716_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2717_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2718_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2719_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2720_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2721_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2722_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_2723_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_2724_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x_2725_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2726_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2727_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(
        v___x_2707_,
        v_inst_2708_,
        v___x_2709_,
        v_toPure_2710_,
        v___x_2711_,
        v___x_2712_,
        v___x_2713_,
        v_toBind_2714_,
        v___f_2715_,
        v_inst_2716_,
        v_inst_2717_,
        v___x_2718_,
        v___x_2719_,
        v___x_2720_,
        v___f_2721_,
        v___x_2722_,
        v_a_2723_,
        v_a_2724_,
        v_x_2725_,
        v___y_2726_,
        v___y_2727_,
    );
    crate::leanh::lean_dec(v___y_2727_);
    return v_res_2728_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(
    mut v_toPure_2729_: *mut crate::leanh::LeanObject,
    mut v___x_2730_: *mut crate::leanh::LeanObject,
    mut v_inst_2731_: *mut crate::leanh::LeanObject,
    mut v___x_2732_: *mut crate::leanh::LeanObject,
    mut v___x_2733_: *mut crate::leanh::LeanObject,
    mut v___x_2734_: *mut crate::leanh::LeanObject,
    mut v_toBind_2735_: *mut crate::leanh::LeanObject,
    mut v_inst_2736_: *mut crate::leanh::LeanObject,
    mut v_inst_2737_: *mut crate::leanh::LeanObject,
    mut v___x_2738_: *mut crate::leanh::LeanObject,
    mut v___x_2739_: *mut crate::leanh::LeanObject,
    mut v___x_2740_: *mut crate::leanh::LeanObject,
    mut v___f_2741_: *mut crate::leanh::LeanObject,
    mut v___x_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_ids_2744_: *mut crate::leanh::LeanObject,
    mut v_ref_2745_: *mut crate::leanh::LeanObject,
    mut v___f_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_6856__overap_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_toPure_2729_);
    v___f_2749_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2749_, 0, v___x_2748_);
    crate::leanh::lean_closure_set(v___f_2749_, 1, v_toPure_2729_);
    crate::leanh::lean_inc(v_toBind_2735_);
    crate::leanh::lean_inc_ref(v___x_2732_);
    v___f_2750_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2750_, 0, v___x_2730_);
    crate::leanh::lean_closure_set(v___f_2750_, 1, v_inst_2731_);
    crate::leanh::lean_closure_set(v___f_2750_, 2, v___x_2748_);
    crate::leanh::lean_closure_set(v___f_2750_, 3, v_toPure_2729_);
    crate::leanh::lean_closure_set(v___f_2750_, 4, v___x_2732_);
    crate::leanh::lean_closure_set(v___f_2750_, 5, v___x_2733_);
    crate::leanh::lean_closure_set(v___f_2750_, 6, v___x_2734_);
    crate::leanh::lean_closure_set(v___f_2750_, 7, v_toBind_2735_);
    crate::leanh::lean_closure_set(v___f_2750_, 8, v___f_2749_);
    crate::leanh::lean_closure_set(v___f_2750_, 9, v_inst_2736_);
    crate::leanh::lean_closure_set(v___f_2750_, 10, v_inst_2737_);
    crate::leanh::lean_closure_set(v___f_2750_, 11, v___x_2738_);
    crate::leanh::lean_closure_set(v___f_2750_, 12, v___x_2739_);
    crate::leanh::lean_closure_set(v___f_2750_, 13, v___x_2740_);
    crate::leanh::lean_closure_set(v___f_2750_, 14, v___f_2741_);
    crate::leanh::lean_closure_set(v___f_2750_, 15, v___x_2742_);
    crate::leanh::lean_closure_set(v___f_2750_, 16, v_a_2743_);
    v_sz_2751_ = lean_array_size(v_ids_2744_);
    v___x_2752_ = 0usize;
    v___x_6856__overap_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2732_,
        v_ids_2744_,
        v___f_2750_,
        v_sz_2751_,
        v___x_2752_,
        v___x_2748_,
    );
    v___x_2754_ = crate::leanh::lean_apply_1(v___x_6856__overap_2753_, v_ref_2745_);
    v___x_2755_ = crate::leanh::lean_apply_4(
        v_toBind_2735_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2754_,
        v___f_2746_,
    );
    return v___x_2755_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_2756_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2757_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_2758_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2759_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2760_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2761_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2762_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_2763_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2764_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2765_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2766_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2767_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___f_2768_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2769_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_2770_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_ids_2771_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_ref_2772_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_2773_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_2774_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(
        v_toPure_2756_,
        v___x_2757_,
        v_inst_2758_,
        v___x_2759_,
        v___x_2760_,
        v___x_2761_,
        v_toBind_2762_,
        v_inst_2763_,
        v_inst_2764_,
        v___x_2765_,
        v___x_2766_,
        v___x_2767_,
        v___f_2768_,
        v___x_2769_,
        v_a_2770_,
        v_ids_2771_,
        v_ref_2772_,
        v___f_2773_,
        v_a_2774_,
    );
    return v_res_2775_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(
    mut v_ids_2776_: *mut crate::leanh::LeanObject,
    mut v___f_2777_: *mut crate::leanh::LeanObject,
    mut v_inst_2778_: *mut crate::leanh::LeanObject,
    mut v_ref_2779_: *mut crate::leanh::LeanObject,
    mut v_toBind_2780_: *mut crate::leanh::LeanObject,
    mut v___f_2781_: *mut crate::leanh::LeanObject,
    mut v_toPure_2782_: *mut crate::leanh::LeanObject,
    mut v___x_2783_: *mut crate::leanh::LeanObject,
    mut v_inst_2784_: *mut crate::leanh::LeanObject,
    mut v___x_2785_: *mut crate::leanh::LeanObject,
    mut v___x_2786_: *mut crate::leanh::LeanObject,
    mut v___x_2787_: *mut crate::leanh::LeanObject,
    mut v_inst_2788_: *mut crate::leanh::LeanObject,
    mut v_inst_2789_: *mut crate::leanh::LeanObject,
    mut v___x_2790_: *mut crate::leanh::LeanObject,
    mut v___x_2791_: *mut crate::leanh::LeanObject,
    mut v___x_2792_: *mut crate::leanh::LeanObject,
    mut v___f_2793_: *mut crate::leanh::LeanObject,
    mut v___x_2794_: *mut crate::leanh::LeanObject,
    mut v_a_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876__overap_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_toBind_2780_, 2);
    crate::leanh::lean_inc_n(v_ref_2779_, 2);
    crate::leanh::lean_inc(v_inst_2778_);
    crate::leanh::lean_inc_n(v_a_2795_, 2);
    crate::leanh::lean_inc_ref(v_ids_2776_);
    v___f_2796_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2796_, 0, v_ids_2776_);
    crate::leanh::lean_closure_set(v___f_2796_, 1, v___f_2777_);
    crate::leanh::lean_closure_set(v___f_2796_, 2, v_a_2795_);
    crate::leanh::lean_closure_set(v___f_2796_, 3, v_inst_2778_);
    crate::leanh::lean_closure_set(v___f_2796_, 4, v_ref_2779_);
    crate::leanh::lean_closure_set(v___f_2796_, 5, v_toBind_2780_);
    crate::leanh::lean_closure_set(v___f_2796_, 6, v___f_2781_);
    crate::leanh::lean_inc_ref(v___x_2786_);
    crate::leanh::lean_inc_ref(v___x_2785_);
    crate::leanh::lean_inc(v___x_2783_);
    v___f_2797_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    crate::leanh::lean_closure_set(v___f_2797_, 0, v_toPure_2782_);
    crate::leanh::lean_closure_set(v___f_2797_, 1, v___x_2783_);
    crate::leanh::lean_closure_set(v___f_2797_, 2, v_inst_2784_);
    crate::leanh::lean_closure_set(v___f_2797_, 3, v___x_2785_);
    crate::leanh::lean_closure_set(v___f_2797_, 4, v___x_2786_);
    crate::leanh::lean_closure_set(v___f_2797_, 5, v___x_2787_);
    crate::leanh::lean_closure_set(v___f_2797_, 6, v_toBind_2780_);
    crate::leanh::lean_closure_set(v___f_2797_, 7, v_inst_2788_);
    crate::leanh::lean_closure_set(v___f_2797_, 8, v_inst_2789_);
    crate::leanh::lean_closure_set(v___f_2797_, 9, v___x_2790_);
    crate::leanh::lean_closure_set(v___f_2797_, 10, v___x_2791_);
    crate::leanh::lean_closure_set(v___f_2797_, 11, v___x_2792_);
    crate::leanh::lean_closure_set(v___f_2797_, 12, v___f_2793_);
    crate::leanh::lean_closure_set(v___f_2797_, 13, v___x_2794_);
    crate::leanh::lean_closure_set(v___f_2797_, 14, v_a_2795_);
    crate::leanh::lean_closure_set(v___f_2797_, 15, v_ids_2776_);
    crate::leanh::lean_closure_set(v___f_2797_, 16, v_ref_2779_);
    crate::leanh::lean_closure_set(v___f_2797_, 17, v___f_2796_);
    v___f_2798_ = crate::leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2798_, 0, v_inst_2778_);
    crate::leanh::lean_closure_set(v___f_2798_, 1, v___x_2783_);
    v___x_6876__overap_2799_ =
        l_Lean_activateScoped___redArg(v___x_2785_, v___x_2786_, v___f_2798_, v_a_2795_);
    v___x_2800_ = crate::leanh::lean_apply_1(v___x_6876__overap_2799_, v_ref_2779_);
    v___x_2801_ = crate::leanh::lean_apply_4(
        v_toBind_2780_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2800_,
        v___f_2797_,
    );
    return v___x_2801_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ids_2802_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___f_2803_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_2804_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ref_2805_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toBind_2806_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_2807_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toPure_2808_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2809_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2810_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2811_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2812_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2813_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_2814_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_2815_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_2816_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2817_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_2818_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_2819_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_2820_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_2821_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(
        v_ids_2802_,
        v___f_2803_,
        v_inst_2804_,
        v_ref_2805_,
        v_toBind_2806_,
        v___f_2807_,
        v_toPure_2808_,
        v___x_2809_,
        v_inst_2810_,
        v___x_2811_,
        v___x_2812_,
        v___x_2813_,
        v_inst_2814_,
        v_inst_2815_,
        v___x_2816_,
        v___x_2817_,
        v___x_2818_,
        v___f_2819_,
        v___x_2820_,
        v_a_2821_,
    );
    return v_res_2822_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(
    mut v_a_2823_: *mut crate::leanh::LeanObject,
    mut v_a_2824_: *mut crate::leanh::LeanObject,
    mut v_inst_2825_: *mut crate::leanh::LeanObject,
    mut v_toBind_2826_: *mut crate::leanh::LeanObject,
    mut v___f_2827_: *mut crate::leanh::LeanObject,
    mut v_____r_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_TSyntax_getId(v_a_2823_);
    v___x_2831_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2831_, 0, v___x_2830_);
    crate::leanh::lean_ctor_set(v___x_2831_, 1, v_a_2824_);
    v___x_2832_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2825_,
        v___x_2831_,
        v___y_2829_,
    );
    v___x_2833_ = crate::leanh::lean_apply_4(
        v_toBind_2826_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2832_,
        v___f_2827_,
    );
    return v___x_2833_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_inst_2836_: *mut crate::leanh::LeanObject,
    mut v_toBind_2837_: *mut crate::leanh::LeanObject,
    mut v___f_2838_: *mut crate::leanh::LeanObject,
    mut v_____r_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(
        v_a_2834_,
        v_a_2835_,
        v_inst_2836_,
        v_toBind_2837_,
        v___f_2838_,
        v_____r_2839_,
        v___y_2840_,
    );
    crate::leanh::lean_dec(v___y_2840_);
    crate::leanh::lean_dec(v_a_2834_);
    return v_res_2841_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(
    mut v___f_2842_: *mut crate::leanh::LeanObject,
    mut v___x_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
    mut v___x_2845_: *mut crate::leanh::LeanObject,
    mut v___x_2846_: *mut crate::leanh::LeanObject,
    mut v___x_2847_: *mut crate::leanh::LeanObject,
    mut v___x_2848_: *mut crate::leanh::LeanObject,
    mut v_a_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_toBind_2851_: *mut crate::leanh::LeanObject,
    mut v___f_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enabled_2854_: u8 = 0;
    v_enabled_2854_ = crate::leanh::lean_ctor_get_uint8(
        v_a_2853_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2854_ == 0 {
        let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2852_);
        crate::leanh::lean_dec(v_toBind_2851_);
        crate::leanh::lean_dec(v_a_2850_);
        crate::leanh::lean_dec(v_a_2849_);
        crate::leanh::lean_dec_ref(v___x_2848_);
        crate::leanh::lean_dec_ref(v___x_2847_);
        crate::leanh::lean_dec_ref(v___x_2846_);
        crate::leanh::lean_dec_ref(v___x_2845_);
        crate::leanh::lean_inc(v___y_2844_);
        v___x_2855_ = crate::leanh::lean_apply_2(v___f_2842_, v___x_2843_, v___y_2844_);
        return v___x_2855_;
    } else {
        let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6905__overap_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2842_);
        v___x_2856_ = crate::leanh::lean_box(0);
        v___x_6905__overap_2857_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2845_,
            v___x_2846_,
            v___x_2847_,
            v___x_2848_,
            v_a_2849_,
            v_a_2850_,
            v___x_2856_,
        );
        crate::leanh::lean_inc(v___y_2844_);
        v___x_2858_ = crate::leanh::lean_apply_1(v___x_6905__overap_2857_, v___y_2844_);
        v___x_2859_ = crate::leanh::lean_apply_4(
            v_toBind_2851_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2858_,
            v___f_2852_,
        );
        return v___x_2859_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(
    mut v___f_2860_: *mut crate::leanh::LeanObject,
    mut v___x_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
    mut v___x_2863_: *mut crate::leanh::LeanObject,
    mut v___x_2864_: *mut crate::leanh::LeanObject,
    mut v___x_2865_: *mut crate::leanh::LeanObject,
    mut v___x_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_toBind_2869_: *mut crate::leanh::LeanObject,
    mut v___f_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(
        v___f_2860_,
        v___x_2861_,
        v___y_2862_,
        v___x_2863_,
        v___x_2864_,
        v___x_2865_,
        v___x_2866_,
        v_a_2867_,
        v_a_2868_,
        v_toBind_2869_,
        v___f_2870_,
        v_a_2871_,
    );
    crate::leanh::lean_dec_ref(v_a_2871_);
    crate::leanh::lean_dec(v___y_2862_);
    return v_res_2872_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(
    mut v___x_2873_: *mut crate::leanh::LeanObject,
    mut v_inst_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_inst_2876_: *mut crate::leanh::LeanObject,
    mut v_toBind_2877_: *mut crate::leanh::LeanObject,
    mut v___f_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___x_2880_: *mut crate::leanh::LeanObject,
    mut v___x_2881_: *mut crate::leanh::LeanObject,
    mut v___x_2882_: *mut crate::leanh::LeanObject,
    mut v___x_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2874_);
    v___x_2885_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2873_, v_inst_2874_);
    v_getInfoState_2886_ = crate::leanh::lean_ctor_get(v_inst_2874_, 0);
    crate::leanh::lean_inc(v_getInfoState_2886_);
    crate::leanh::lean_dec_ref(v_inst_2874_);
    crate::leanh::lean_inc_n(v_toBind_2877_, 2);
    crate::leanh::lean_inc(v_a_2884_);
    crate::leanh::lean_inc(v_a_2875_);
    v___f_2887_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2887_, 0, v_a_2875_);
    crate::leanh::lean_closure_set(v___f_2887_, 1, v_a_2884_);
    crate::leanh::lean_closure_set(v___f_2887_, 2, v_inst_2876_);
    crate::leanh::lean_closure_set(v___f_2887_, 3, v_toBind_2877_);
    crate::leanh::lean_closure_set(v___f_2887_, 4, v___f_2878_);
    crate::leanh::lean_inc_n(v___y_2879_, 2);
    crate::leanh::lean_inc_ref(v___f_2887_);
    v___f_2888_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2888_, 0, v___f_2887_);
    crate::leanh::lean_closure_set(v___f_2888_, 1, v___y_2879_);
    v___f_2889_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2889_, 0, v___f_2887_);
    crate::leanh::lean_closure_set(v___f_2889_, 1, v___x_2880_);
    crate::leanh::lean_closure_set(v___f_2889_, 2, v___y_2879_);
    crate::leanh::lean_closure_set(v___f_2889_, 3, v___x_2881_);
    crate::leanh::lean_closure_set(v___f_2889_, 4, v___x_2885_);
    crate::leanh::lean_closure_set(v___f_2889_, 5, v___x_2882_);
    crate::leanh::lean_closure_set(v___f_2889_, 6, v___x_2883_);
    crate::leanh::lean_closure_set(v___f_2889_, 7, v_a_2875_);
    crate::leanh::lean_closure_set(v___f_2889_, 8, v_a_2884_);
    crate::leanh::lean_closure_set(v___f_2889_, 9, v_toBind_2877_);
    crate::leanh::lean_closure_set(v___f_2889_, 10, v___f_2888_);
    v___x_2890_ = crate::leanh::lean_apply_4(
        v_toBind_2877_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInfoState_2886_,
        v___f_2889_,
    );
    return v___x_2890_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(
    mut v___x_2891_: *mut crate::leanh::LeanObject,
    mut v_inst_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
    mut v_inst_2894_: *mut crate::leanh::LeanObject,
    mut v_toBind_2895_: *mut crate::leanh::LeanObject,
    mut v___f_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___x_2898_: *mut crate::leanh::LeanObject,
    mut v___x_2899_: *mut crate::leanh::LeanObject,
    mut v___x_2900_: *mut crate::leanh::LeanObject,
    mut v___x_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2903_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(
        v___x_2891_,
        v_inst_2892_,
        v_a_2893_,
        v_inst_2894_,
        v_toBind_2895_,
        v___f_2896_,
        v___y_2897_,
        v___x_2898_,
        v___x_2899_,
        v___x_2900_,
        v___x_2901_,
        v_a_2902_,
    );
    crate::leanh::lean_dec(v___y_2897_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(
    mut v___x_2904_: *mut crate::leanh::LeanObject,
    mut v_inst_2905_: *mut crate::leanh::LeanObject,
    mut v_inst_2906_: *mut crate::leanh::LeanObject,
    mut v_toBind_2907_: *mut crate::leanh::LeanObject,
    mut v___f_2908_: *mut crate::leanh::LeanObject,
    mut v___x_2909_: *mut crate::leanh::LeanObject,
    mut v___x_2910_: *mut crate::leanh::LeanObject,
    mut v___x_2911_: *mut crate::leanh::LeanObject,
    mut v___x_2912_: *mut crate::leanh::LeanObject,
    mut v_inst_2913_: *mut crate::leanh::LeanObject,
    mut v_inst_2914_: *mut crate::leanh::LeanObject,
    mut v___x_2915_: *mut crate::leanh::LeanObject,
    mut v___x_2916_: *mut crate::leanh::LeanObject,
    mut v___x_2917_: *mut crate::leanh::LeanObject,
    mut v___f_2918_: *mut crate::leanh::LeanObject,
    mut v___x_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_x_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942__overap_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___x_2911_);
    crate::leanh::lean_inc_ref(v___x_2910_);
    crate::leanh::lean_inc_n(v___y_2924_, 2);
    crate::leanh::lean_inc(v_toBind_2907_);
    crate::leanh::lean_inc(v_a_2921_);
    crate::leanh::lean_inc(v___x_2904_);
    v___f_2925_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2925_, 0, v___x_2904_);
    crate::leanh::lean_closure_set(v___f_2925_, 1, v_inst_2905_);
    crate::leanh::lean_closure_set(v___f_2925_, 2, v_a_2921_);
    crate::leanh::lean_closure_set(v___f_2925_, 3, v_inst_2906_);
    crate::leanh::lean_closure_set(v___f_2925_, 4, v_toBind_2907_);
    crate::leanh::lean_closure_set(v___f_2925_, 5, v___f_2908_);
    crate::leanh::lean_closure_set(v___f_2925_, 6, v___y_2924_);
    crate::leanh::lean_closure_set(v___f_2925_, 7, v___x_2909_);
    crate::leanh::lean_closure_set(v___f_2925_, 8, v___x_2910_);
    crate::leanh::lean_closure_set(v___f_2925_, 9, v___x_2911_);
    crate::leanh::lean_closure_set(v___f_2925_, 10, v___x_2912_);
    v___x_2926_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2904_, v_inst_2913_);
    v___x_2927_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_2927_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2927_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2927_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2927_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2927_, 4, v_inst_2914_);
    v___x_6942__overap_2928_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
        v___x_2910_,
        v___x_2911_,
        v___x_2915_,
        v___x_2916_,
        v___x_2917_,
        v___f_2918_,
        v___x_2926_,
        v___x_2927_,
        v___x_2919_,
        v_a_2920_,
        v_a_2921_,
    );
    v___x_2929_ = crate::leanh::lean_apply_1(v___x_6942__overap_2928_, v___y_2924_);
    v___x_2930_ = crate::leanh::lean_apply_4(
        v_toBind_2907_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2929_,
        v___f_2925_,
    );
    return v___x_2930_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2931_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_2932_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_2933_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toBind_2934_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_2935_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2936_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2937_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2938_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2939_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_2940_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2941_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2942_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2943_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2944_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2945_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2946_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_2947_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_2948_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x_2949_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2950_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2951_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(
        v___x_2931_,
        v_inst_2932_,
        v_inst_2933_,
        v_toBind_2934_,
        v___f_2935_,
        v___x_2936_,
        v___x_2937_,
        v___x_2938_,
        v___x_2939_,
        v_inst_2940_,
        v_inst_2941_,
        v___x_2942_,
        v___x_2943_,
        v___x_2944_,
        v___f_2945_,
        v___x_2946_,
        v_a_2947_,
        v_a_2948_,
        v_x_2949_,
        v___y_2950_,
        v___y_2951_,
    );
    crate::leanh::lean_dec(v___y_2951_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(
    mut v_toPure_2953_: *mut crate::leanh::LeanObject,
    mut v___x_2954_: *mut crate::leanh::LeanObject,
    mut v_inst_2955_: *mut crate::leanh::LeanObject,
    mut v_inst_2956_: *mut crate::leanh::LeanObject,
    mut v_toBind_2957_: *mut crate::leanh::LeanObject,
    mut v___x_2958_: *mut crate::leanh::LeanObject,
    mut v___x_2959_: *mut crate::leanh::LeanObject,
    mut v___x_2960_: *mut crate::leanh::LeanObject,
    mut v_inst_2961_: *mut crate::leanh::LeanObject,
    mut v_inst_2962_: *mut crate::leanh::LeanObject,
    mut v___x_2963_: *mut crate::leanh::LeanObject,
    mut v___x_2964_: *mut crate::leanh::LeanObject,
    mut v___x_2965_: *mut crate::leanh::LeanObject,
    mut v___f_2966_: *mut crate::leanh::LeanObject,
    mut v___x_2967_: *mut crate::leanh::LeanObject,
    mut v_ids_2968_: *mut crate::leanh::LeanObject,
    mut v_ref_2969_: *mut crate::leanh::LeanObject,
    mut v___f_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2975_: usize = 0;
    let mut v___x_2976_: usize = 0;
    let mut v___x_6962__overap_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = crate::leanh::lean_box(0);
    v___f_2973_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2973_, 0, v___x_2972_);
    crate::leanh::lean_closure_set(v___f_2973_, 1, v_toPure_2953_);
    crate::leanh::lean_inc_ref(v___x_2958_);
    crate::leanh::lean_inc(v_toBind_2957_);
    v___f_2974_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2974_, 0, v___x_2954_);
    crate::leanh::lean_closure_set(v___f_2974_, 1, v_inst_2955_);
    crate::leanh::lean_closure_set(v___f_2974_, 2, v_inst_2956_);
    crate::leanh::lean_closure_set(v___f_2974_, 3, v_toBind_2957_);
    crate::leanh::lean_closure_set(v___f_2974_, 4, v___f_2973_);
    crate::leanh::lean_closure_set(v___f_2974_, 5, v___x_2972_);
    crate::leanh::lean_closure_set(v___f_2974_, 6, v___x_2958_);
    crate::leanh::lean_closure_set(v___f_2974_, 7, v___x_2959_);
    crate::leanh::lean_closure_set(v___f_2974_, 8, v___x_2960_);
    crate::leanh::lean_closure_set(v___f_2974_, 9, v_inst_2961_);
    crate::leanh::lean_closure_set(v___f_2974_, 10, v_inst_2962_);
    crate::leanh::lean_closure_set(v___f_2974_, 11, v___x_2963_);
    crate::leanh::lean_closure_set(v___f_2974_, 12, v___x_2964_);
    crate::leanh::lean_closure_set(v___f_2974_, 13, v___x_2965_);
    crate::leanh::lean_closure_set(v___f_2974_, 14, v___f_2966_);
    crate::leanh::lean_closure_set(v___f_2974_, 15, v___x_2967_);
    crate::leanh::lean_closure_set(v___f_2974_, 16, v_a_2971_);
    v_sz_2975_ = lean_array_size(v_ids_2968_);
    v___x_2976_ = 0usize;
    v___x_6962__overap_2977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2958_,
        v_ids_2968_,
        v___f_2974_,
        v_sz_2975_,
        v___x_2976_,
        v___x_2972_,
    );
    v___x_2978_ = crate::leanh::lean_apply_1(v___x_6962__overap_2977_, v_ref_2969_);
    v___x_2979_ = crate::leanh::lean_apply_4(
        v_toBind_2957_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2978_,
        v___f_2970_,
    );
    return v___x_2979_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_2980_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2981_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_2982_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_2983_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toBind_2984_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2985_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2986_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2987_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2988_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_2989_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2990_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2991_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2992_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_2993_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_2994_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_ids_2995_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_ref_2996_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_2997_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_2998_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(
        v_toPure_2980_,
        v___x_2981_,
        v_inst_2982_,
        v_inst_2983_,
        v_toBind_2984_,
        v___x_2985_,
        v___x_2986_,
        v___x_2987_,
        v_inst_2988_,
        v_inst_2989_,
        v___x_2990_,
        v___x_2991_,
        v___x_2992_,
        v___f_2993_,
        v___x_2994_,
        v_ids_2995_,
        v_ref_2996_,
        v___f_2997_,
        v_a_2998_,
    );
    return v_res_2999_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(
    mut v_inst_3000_: *mut crate::leanh::LeanObject,
    mut v___x_3001_: *mut crate::leanh::LeanObject,
    mut v___x_3002_: *mut crate::leanh::LeanObject,
    mut v___x_3003_: *mut crate::leanh::LeanObject,
    mut v_toBind_3004_: *mut crate::leanh::LeanObject,
    mut v___f_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_x_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982__overap_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3010_ = crate::leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3010_, 0, v_inst_3000_);
    crate::leanh::lean_closure_set(v___f_3010_, 1, v___x_3001_);
    v___x_6982__overap_3011_ =
        l_Lean_activateScoped___redArg(v___x_3002_, v___x_3003_, v___f_3010_, v_a_3006_);
    crate::leanh::lean_inc(v___y_3009_);
    v___x_3012_ = crate::leanh::lean_apply_1(v___x_6982__overap_3011_, v___y_3009_);
    v___x_3013_ = crate::leanh::lean_apply_4(
        v_toBind_3004_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3012_,
        v___f_3005_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(
    mut v_inst_3014_: *mut crate::leanh::LeanObject,
    mut v___x_3015_: *mut crate::leanh::LeanObject,
    mut v___x_3016_: *mut crate::leanh::LeanObject,
    mut v___x_3017_: *mut crate::leanh::LeanObject,
    mut v_toBind_3018_: *mut crate::leanh::LeanObject,
    mut v___f_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_x_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3024_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(
        v_inst_3014_,
        v___x_3015_,
        v___x_3016_,
        v___x_3017_,
        v_toBind_3018_,
        v___f_3019_,
        v_a_3020_,
        v_x_3021_,
        v___y_3022_,
        v___y_3023_,
    );
    crate::leanh::lean_dec(v___y_3023_);
    return v_res_3024_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
    mut v___x_3025_: *mut crate::leanh::LeanObject,
    mut v___f_3026_: *mut crate::leanh::LeanObject,
    mut v___x_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v_toBind_3029_: *mut crate::leanh::LeanObject,
    mut v___f_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6989__overap_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6989__overap_3032_ =
        l_List_forIn_x27_loop___redArg(v___x_3025_, v___f_3026_, v_a_3031_, v___x_3027_);
    crate::leanh::lean_inc(v___y_3028_);
    v___x_3033_ = crate::leanh::lean_apply_1(v___x_6989__overap_3032_, v___y_3028_);
    v___x_3034_ = crate::leanh::lean_apply_4(
        v_toBind_3029_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3033_,
        v___f_3030_,
    );
    return v___x_3034_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(
    mut v___x_3035_: *mut crate::leanh::LeanObject,
    mut v___f_3036_: *mut crate::leanh::LeanObject,
    mut v___x_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v_toBind_3039_: *mut crate::leanh::LeanObject,
    mut v___f_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
        v___x_3035_,
        v___f_3036_,
        v___x_3037_,
        v___y_3038_,
        v_toBind_3039_,
        v___f_3040_,
        v_a_3041_,
    );
    crate::leanh::lean_dec(v_a_3041_);
    crate::leanh::lean_dec(v___y_3038_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(
    mut v_inst_3045_: *mut crate::leanh::LeanObject,
    mut v_inst_3046_: *mut crate::leanh::LeanObject,
    mut v_inst_3047_: *mut crate::leanh::LeanObject,
    mut v___x_3048_: *mut crate::leanh::LeanObject,
    mut v_toBind_3049_: *mut crate::leanh::LeanObject,
    mut v___f_3050_: *mut crate::leanh::LeanObject,
    mut v___x_3051_: *mut crate::leanh::LeanObject,
    mut v___f_3052_: *mut crate::leanh::LeanObject,
    mut v_inst_3053_: *mut crate::leanh::LeanObject,
    mut v_inst_3054_: *mut crate::leanh::LeanObject,
    mut v_inst_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_x_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019__overap_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_inst_3046_);
                v___x_3060_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3045_, v_inst_3046_);
                v_getEnv_3061_ = crate::leanh::lean_ctor_get(v_inst_3047_, 0);
                v_modifyEnv_3062_ = crate::leanh::lean_ctor_get(v_inst_3047_, 1);
                v_isSharedCheck_3085_ = (!crate::leanh::lean_is_exclusive(v_inst_3047_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_3064_ = v_inst_3047_;
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyEnv_3062_);
                    crate::leanh::lean_inc(v_getEnv_3061_);
                    crate::leanh::lean_dec(v_inst_3047_);
                    v___x_3064_ = crate::leanh::lean_box(0);
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3066_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3067_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3067_, 0, v_modifyEnv_3062_);
                crate::leanh::lean_closure_set(v___f_3067_, 1, v___x_3066_);
                v___x_3068_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3068_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3068_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3068_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3068_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3068_, 4, v_getEnv_3061_);
                if v_isShared_3065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3064_, 1, v___f_3067_);
                    crate::leanh::lean_ctor_set(v___x_3064_, 0, v___x_3068_);
                    v___x_3070_ = v___x_3064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___f_3067_);
                    v___x_3070_ = v_reuseFailAlloc_3084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_n(v_toBind_3049_, 2);
                crate::leanh::lean_inc_ref(v___x_3070_);
                crate::leanh::lean_inc_ref_n(v___x_3048_, 3);
                v___f_3071_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed
                        as *mut core::ffi::c_void,
                    10,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_3071_, 0, v_inst_3046_);
                crate::leanh::lean_closure_set(v___f_3071_, 1, v___x_3066_);
                crate::leanh::lean_closure_set(v___f_3071_, 2, v___x_3048_);
                crate::leanh::lean_closure_set(v___f_3071_, 3, v___x_3070_);
                crate::leanh::lean_closure_set(v___f_3071_, 4, v_toBind_3049_);
                crate::leanh::lean_closure_set(v___f_3071_, 5, v___f_3050_);
                crate::leanh::lean_inc_n(v___y_3059_, 2);
                v___f_3072_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_3072_, 0, v___x_3048_);
                crate::leanh::lean_closure_set(v___f_3072_, 1, v___f_3071_);
                crate::leanh::lean_closure_set(v___f_3072_, 2, v___x_3051_);
                crate::leanh::lean_closure_set(v___f_3072_, 3, v___y_3059_);
                crate::leanh::lean_closure_set(v___f_3072_, 4, v_toBind_3049_);
                crate::leanh::lean_closure_set(v___f_3072_, 5, v___f_3052_);
                crate::leanh::lean_inc_ref(v_inst_3053_);
                v___f_3073_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3073_, 0, v_inst_3053_);
                v___f_3074_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3074_, 0, v_inst_3053_);
                v___x_3075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3075_, 0, v___f_3073_);
                crate::leanh::lean_ctor_set(v___x_3075_, 1, v___f_3074_);
                v___x_3076_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3077_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3066_,
                    v___x_3076_,
                    v_inst_3054_,
                );
                v___f_3078_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3078_, 0, v_inst_3055_);
                crate::leanh::lean_closure_set(v___f_3078_, 1, v___x_3066_);
                v___x_3079_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3078_,
                    v___x_3048_,
                );
                v___x_3080_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3075_);
                crate::leanh::lean_ctor_set(v___x_3080_, 1, v___x_3077_);
                crate::leanh::lean_ctor_set(v___x_3080_, 2, v___x_3079_);
                v___x_7019__overap_3081_ = l_Lean_resolveNamespace___redArg(
                    v___x_3048_,
                    v___x_3060_,
                    v___x_3070_,
                    v___x_3080_,
                    v_a_3056_,
                );
                v___x_3082_ = crate::leanh::lean_apply_1(v___x_7019__overap_3081_, v___y_3059_);
                v___x_3083_ = crate::leanh::lean_apply_4(
                    v_toBind_3049_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3082_,
                    v___f_3072_,
                );
                return v___x_3083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(
    mut v_inst_3086_: *mut crate::leanh::LeanObject,
    mut v_inst_3087_: *mut crate::leanh::LeanObject,
    mut v_inst_3088_: *mut crate::leanh::LeanObject,
    mut v___x_3089_: *mut crate::leanh::LeanObject,
    mut v_toBind_3090_: *mut crate::leanh::LeanObject,
    mut v___f_3091_: *mut crate::leanh::LeanObject,
    mut v___x_3092_: *mut crate::leanh::LeanObject,
    mut v___f_3093_: *mut crate::leanh::LeanObject,
    mut v_inst_3094_: *mut crate::leanh::LeanObject,
    mut v_inst_3095_: *mut crate::leanh::LeanObject,
    mut v_inst_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_x_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3101_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(
        v_inst_3086_,
        v_inst_3087_,
        v_inst_3088_,
        v___x_3089_,
        v_toBind_3090_,
        v___f_3091_,
        v___x_3092_,
        v___f_3093_,
        v_inst_3094_,
        v_inst_3095_,
        v_inst_3096_,
        v_a_3097_,
        v_x_3098_,
        v___y_3099_,
        v___y_3100_,
    );
    crate::leanh::lean_dec(v___y_3100_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(
    mut v_inst_3102_: *mut crate::leanh::LeanObject,
    mut v___x_3103_: *mut crate::leanh::LeanObject,
    mut v___x_3104_: *mut crate::leanh::LeanObject,
    mut v___x_3105_: *mut crate::leanh::LeanObject,
    mut v_a_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v_toBind_3108_: *mut crate::leanh::LeanObject,
    mut v___f_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037__overap_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3111_ = crate::leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3111_, 0, v_inst_3102_);
    crate::leanh::lean_closure_set(v___f_3111_, 1, v___x_3103_);
    v___x_7037__overap_3112_ =
        l_Lean_activateScoped___redArg(v___x_3104_, v___x_3105_, v___f_3111_, v_a_3106_);
    crate::leanh::lean_inc(v___y_3107_);
    v___x_3113_ = crate::leanh::lean_apply_1(v___x_7037__overap_3112_, v___y_3107_);
    v___x_3114_ = crate::leanh::lean_apply_4(
        v_toBind_3108_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3113_,
        v___f_3109_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(
    mut v_inst_3115_: *mut crate::leanh::LeanObject,
    mut v___x_3116_: *mut crate::leanh::LeanObject,
    mut v___x_3117_: *mut crate::leanh::LeanObject,
    mut v___x_3118_: *mut crate::leanh::LeanObject,
    mut v_a_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v_toBind_3121_: *mut crate::leanh::LeanObject,
    mut v___f_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3124_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(
        v_inst_3115_,
        v___x_3116_,
        v___x_3117_,
        v___x_3118_,
        v_a_3119_,
        v___y_3120_,
        v_toBind_3121_,
        v___f_3122_,
        v_a_3123_,
    );
    crate::leanh::lean_dec(v___y_3120_);
    return v_res_3124_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(
    mut v_inst_3125_: *mut crate::leanh::LeanObject,
    mut v___x_3126_: *mut crate::leanh::LeanObject,
    mut v___x_3127_: *mut crate::leanh::LeanObject,
    mut v___x_3128_: *mut crate::leanh::LeanObject,
    mut v_toBind_3129_: *mut crate::leanh::LeanObject,
    mut v___f_3130_: *mut crate::leanh::LeanObject,
    mut v___x_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
    mut v_x_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_3129_);
    crate::leanh::lean_inc(v___y_3135_);
    crate::leanh::lean_inc(v_a_3132_);
    crate::leanh::lean_inc(v_inst_3125_);
    v___f_3136_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_3136_, 0, v_inst_3125_);
    crate::leanh::lean_closure_set(v___f_3136_, 1, v___x_3126_);
    crate::leanh::lean_closure_set(v___f_3136_, 2, v___x_3127_);
    crate::leanh::lean_closure_set(v___f_3136_, 3, v___x_3128_);
    crate::leanh::lean_closure_set(v___f_3136_, 4, v_a_3132_);
    crate::leanh::lean_closure_set(v___f_3136_, 5, v___y_3135_);
    crate::leanh::lean_closure_set(v___f_3136_, 6, v_toBind_3129_);
    crate::leanh::lean_closure_set(v___f_3136_, 7, v___f_3130_);
    v___x_3137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3137_, 0, v_a_3132_);
    crate::leanh::lean_ctor_set(v___x_3137_, 1, v___x_3131_);
    v___x_3138_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_3125_,
        v___x_3137_,
        v___y_3135_,
    );
    v___x_3139_ = crate::leanh::lean_apply_4(
        v_toBind_3129_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3138_,
        v___f_3136_,
    );
    return v___x_3139_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(
    mut v_inst_3140_: *mut crate::leanh::LeanObject,
    mut v___x_3141_: *mut crate::leanh::LeanObject,
    mut v___x_3142_: *mut crate::leanh::LeanObject,
    mut v___x_3143_: *mut crate::leanh::LeanObject,
    mut v_toBind_3144_: *mut crate::leanh::LeanObject,
    mut v___f_3145_: *mut crate::leanh::LeanObject,
    mut v___x_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3151_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(
        v_inst_3140_,
        v___x_3141_,
        v___x_3142_,
        v___x_3143_,
        v_toBind_3144_,
        v___f_3145_,
        v___x_3146_,
        v_a_3147_,
        v_x_3148_,
        v___y_3149_,
        v___y_3150_,
    );
    crate::leanh::lean_dec(v___y_3150_);
    return v_res_3151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(
    mut v_inst_3152_: *mut crate::leanh::LeanObject,
    mut v_inst_3153_: *mut crate::leanh::LeanObject,
    mut v_inst_3154_: *mut crate::leanh::LeanObject,
    mut v___x_3155_: *mut crate::leanh::LeanObject,
    mut v_toBind_3156_: *mut crate::leanh::LeanObject,
    mut v___f_3157_: *mut crate::leanh::LeanObject,
    mut v___x_3158_: *mut crate::leanh::LeanObject,
    mut v___x_3159_: *mut crate::leanh::LeanObject,
    mut v___f_3160_: *mut crate::leanh::LeanObject,
    mut v_inst_3161_: *mut crate::leanh::LeanObject,
    mut v_inst_3162_: *mut crate::leanh::LeanObject,
    mut v_inst_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_x_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088__overap_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_inst_3153_);
                v___x_3168_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3152_, v_inst_3153_);
                v_getEnv_3169_ = crate::leanh::lean_ctor_get(v_inst_3154_, 0);
                v_modifyEnv_3170_ = crate::leanh::lean_ctor_get(v_inst_3154_, 1);
                v_isSharedCheck_3193_ = (!crate::leanh::lean_is_exclusive(v_inst_3154_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v___x_3172_ = v_inst_3154_;
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyEnv_3170_);
                    crate::leanh::lean_inc(v_getEnv_3169_);
                    crate::leanh::lean_dec(v_inst_3154_);
                    v___x_3172_ = crate::leanh::lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3175_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3175_, 0, v_modifyEnv_3170_);
                crate::leanh::lean_closure_set(v___f_3175_, 1, v___x_3174_);
                v___x_3176_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3176_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3176_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3176_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3176_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3176_, 4, v_getEnv_3169_);
                if v_isShared_3173_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3172_, 1, v___f_3175_);
                    crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3176_);
                    v___x_3178_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___f_3175_);
                    v___x_3178_ = v_reuseFailAlloc_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_n(v_toBind_3156_, 2);
                crate::leanh::lean_inc_ref(v___x_3178_);
                crate::leanh::lean_inc_ref_n(v___x_3155_, 3);
                v___f_3179_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_3179_, 0, v_inst_3153_);
                crate::leanh::lean_closure_set(v___f_3179_, 1, v___x_3174_);
                crate::leanh::lean_closure_set(v___f_3179_, 2, v___x_3155_);
                crate::leanh::lean_closure_set(v___f_3179_, 3, v___x_3178_);
                crate::leanh::lean_closure_set(v___f_3179_, 4, v_toBind_3156_);
                crate::leanh::lean_closure_set(v___f_3179_, 5, v___f_3157_);
                crate::leanh::lean_closure_set(v___f_3179_, 6, v___x_3158_);
                crate::leanh::lean_inc_n(v___y_3167_, 2);
                v___f_3180_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_3180_, 0, v___x_3155_);
                crate::leanh::lean_closure_set(v___f_3180_, 1, v___f_3179_);
                crate::leanh::lean_closure_set(v___f_3180_, 2, v___x_3159_);
                crate::leanh::lean_closure_set(v___f_3180_, 3, v___y_3167_);
                crate::leanh::lean_closure_set(v___f_3180_, 4, v_toBind_3156_);
                crate::leanh::lean_closure_set(v___f_3180_, 5, v___f_3160_);
                crate::leanh::lean_inc_ref(v_inst_3161_);
                v___f_3181_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3181_, 0, v_inst_3161_);
                v___f_3182_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3182_, 0, v_inst_3161_);
                v___x_3183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3183_, 0, v___f_3181_);
                crate::leanh::lean_ctor_set(v___x_3183_, 1, v___f_3182_);
                v___x_3184_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3185_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3174_,
                    v___x_3184_,
                    v_inst_3162_,
                );
                v___f_3186_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3186_, 0, v_inst_3163_);
                crate::leanh::lean_closure_set(v___f_3186_, 1, v___x_3174_);
                v___x_3187_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3186_,
                    v___x_3155_,
                );
                v___x_3188_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3188_, 0, v___x_3183_);
                crate::leanh::lean_ctor_set(v___x_3188_, 1, v___x_3185_);
                crate::leanh::lean_ctor_set(v___x_3188_, 2, v___x_3187_);
                v___x_7088__overap_3189_ = l_Lean_resolveNamespace___redArg(
                    v___x_3155_,
                    v___x_3168_,
                    v___x_3178_,
                    v___x_3188_,
                    v_a_3164_,
                );
                v___x_3190_ = crate::leanh::lean_apply_1(v___x_7088__overap_3189_, v___y_3167_);
                v___x_3191_ = crate::leanh::lean_apply_4(
                    v_toBind_3156_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3190_,
                    v___f_3180_,
                );
                return v___x_3191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(
    mut v_inst_3194_: *mut crate::leanh::LeanObject,
    mut v_inst_3195_: *mut crate::leanh::LeanObject,
    mut v_inst_3196_: *mut crate::leanh::LeanObject,
    mut v___x_3197_: *mut crate::leanh::LeanObject,
    mut v_toBind_3198_: *mut crate::leanh::LeanObject,
    mut v___f_3199_: *mut crate::leanh::LeanObject,
    mut v___x_3200_: *mut crate::leanh::LeanObject,
    mut v___x_3201_: *mut crate::leanh::LeanObject,
    mut v___f_3202_: *mut crate::leanh::LeanObject,
    mut v_inst_3203_: *mut crate::leanh::LeanObject,
    mut v_inst_3204_: *mut crate::leanh::LeanObject,
    mut v_inst_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_x_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3210_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(
        v_inst_3194_,
        v_inst_3195_,
        v_inst_3196_,
        v___x_3197_,
        v_toBind_3198_,
        v___f_3199_,
        v___x_3200_,
        v___x_3201_,
        v___f_3202_,
        v_inst_3203_,
        v_inst_3204_,
        v_inst_3205_,
        v_a_3206_,
        v_x_3207_,
        v___y_3208_,
        v___y_3209_,
    );
    crate::leanh::lean_dec(v___y_3209_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(
    mut v_toPure_3238_: *mut crate::leanh::LeanObject,
    mut v_inst_3239_: *mut crate::leanh::LeanObject,
    mut v_toBind_3240_: *mut crate::leanh::LeanObject,
    mut v___x_3241_: u8,
    mut v___x_3242_: *mut crate::leanh::LeanObject,
    mut v___x_3243_: *mut crate::leanh::LeanObject,
    mut v___x_3244_: *mut crate::leanh::LeanObject,
    mut v_stx_3245_: *mut crate::leanh::LeanObject,
    mut v___f_3246_: *mut crate::leanh::LeanObject,
    mut v_inst_3247_: *mut crate::leanh::LeanObject,
    mut v_inst_3248_: *mut crate::leanh::LeanObject,
    mut v_inst_3249_: *mut crate::leanh::LeanObject,
    mut v___f_3250_: *mut crate::leanh::LeanObject,
    mut v___f_3251_: *mut crate::leanh::LeanObject,
    mut v_inst_3252_: *mut crate::leanh::LeanObject,
    mut v_inst_3253_: *mut crate::leanh::LeanObject,
    mut v___x_3254_: *mut crate::leanh::LeanObject,
    mut v_inst_3255_: *mut crate::leanh::LeanObject,
    mut v_inst_3256_: *mut crate::leanh::LeanObject,
    mut v_inst_3257_: *mut crate::leanh::LeanObject,
    mut v___f_3258_: *mut crate::leanh::LeanObject,
    mut v_ref_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: u8 = 0;
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___f_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125__overap_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151__overap_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3303_: usize = 0;
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v_tos_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_froms_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179__overap_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___f_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223__overap_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___f_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244__overap_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v___f_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nss_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3423_: usize = 0;
    let mut v___x_3424_: usize = 0;
    let mut v___x_7255__overap_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nss_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3437_: usize = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_7267__overap_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_toBind_3240_);
                crate::leanh::lean_inc(v_inst_3239_);
                crate::leanh::lean_inc(v_ref_3259_);
                crate::leanh::lean_inc(v_toPure_3238_);
                v___f_3260_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3260_, 0, v_toPure_3238_);
                crate::leanh::lean_closure_set(v___f_3260_, 1, v_ref_3259_);
                crate::leanh::lean_closure_set(v___f_3260_, 2, v_inst_3239_);
                crate::leanh::lean_closure_set(v___f_3260_, 3, v_toBind_3240_);
                if v___x_3241_ == 0 {
                    v___x_3261_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0;
                    crate::leanh::lean_inc_ref(v___x_3244_);
                    crate::leanh::lean_inc_ref(v___x_3243_);
                    crate::leanh::lean_inc_ref(v___x_3242_);
                    v___x_3262_ =
                        l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3261_);
                    crate::leanh::lean_inc(v_stx_3245_);
                    v___x_3263_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3262_);
                    crate::leanh::lean_dec(v___x_3262_);
                    if v___x_3263_ == 0 {
                        v___x_3264_ =
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1;
                        crate::leanh::lean_inc_ref(v___x_3244_);
                        crate::leanh::lean_inc_ref(v___x_3243_);
                        crate::leanh::lean_inc_ref(v___x_3242_);
                        v___x_3265_ =
                            l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3264_);
                        crate::leanh::lean_inc(v_stx_3245_);
                        v___x_3266_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3265_);
                        crate::leanh::lean_dec(v___x_3265_);
                        if v___x_3266_ == 0 {
                            v___x_3267_ =
                                l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2;
                            crate::leanh::lean_inc_ref(v___x_3244_);
                            crate::leanh::lean_inc_ref(v___x_3243_);
                            crate::leanh::lean_inc_ref(v___x_3242_);
                            v___x_3268_ = l_Lean_Name_mkStr4(
                                v___x_3242_,
                                v___x_3243_,
                                v___x_3244_,
                                v___x_3267_,
                            );
                            crate::leanh::lean_inc(v_stx_3245_);
                            v___x_3269_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3268_);
                            crate::leanh::lean_dec(v___x_3268_);
                            if v___x_3269_ == 0 {
                                crate::leanh::lean_dec_ref(v___f_3258_);
                                v___x_3270_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3;
                                crate::leanh::lean_inc_ref(v___x_3244_);
                                crate::leanh::lean_inc_ref(v___x_3243_);
                                crate::leanh::lean_inc_ref(v___x_3242_);
                                v___x_3271_ = l_Lean_Name_mkStr4(
                                    v___x_3242_,
                                    v___x_3243_,
                                    v___x_3244_,
                                    v___x_3270_,
                                );
                                crate::leanh::lean_inc(v_stx_3245_);
                                v___x_3272_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3271_);
                                crate::leanh::lean_dec(v___x_3271_);
                                if v___x_3272_ == 0 {
                                    crate::leanh::lean_dec(v_inst_3257_);
                                    crate::leanh::lean_dec_ref(v_inst_3256_);
                                    crate::leanh::lean_dec_ref(v_inst_3255_);
                                    crate::leanh::lean_dec_ref(v___x_3254_);
                                    crate::leanh::lean_dec(v_inst_3253_);
                                    crate::leanh::lean_dec_ref(v_inst_3252_);
                                    crate::leanh::lean_dec_ref(v___f_3251_);
                                    crate::leanh::lean_dec_ref(v___f_3250_);
                                    crate::leanh::lean_dec_ref(v_inst_3249_);
                                    crate::leanh::lean_dec_ref(v_inst_3248_);
                                    crate::leanh::lean_dec(v_stx_3245_);
                                    crate::leanh::lean_dec_ref(v___x_3244_);
                                    crate::leanh::lean_dec_ref(v___x_3243_);
                                    crate::leanh::lean_dec_ref(v___x_3242_);
                                    crate::leanh::lean_dec(v_inst_3239_);
                                    crate::leanh::lean_dec(v_toPure_3238_);
                                    crate::leanh::lean_inc(v_ref_3259_);
                                    v___f_3273_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3273_, 0, v___f_3246_);
                                    crate::leanh::lean_closure_set(v___f_3273_, 1, v_ref_3259_);
                                    crate::leanh::lean_inc_ref(v_inst_3247_);
                                    v___f_3274_ = crate::leanh::lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3274_, 0, v_inst_3247_);
                                    v___f_3275_ = crate::leanh::lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                                            as *mut core::ffi::c_void,
                                        5,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3275_, 0, v_inst_3247_);
                                    v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3276_, 0, v___f_3274_);
                                    crate::leanh::lean_ctor_set(v___x_3276_, 1, v___f_3275_);
                                    v___x_7125__overap_3277_ =
                                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3276_);
                                    v___x_3278_ = crate::leanh::lean_apply_1(
                                        v___x_7125__overap_3277_,
                                        v_ref_3259_,
                                    );
                                    crate::leanh::lean_inc(v_toBind_3240_);
                                    v___x_3279_ = crate::leanh::lean_apply_4(
                                        v_toBind_3240_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_3278_,
                                        v___f_3273_,
                                    );
                                    v___x_3280_ = crate::leanh::lean_apply_4(
                                        v_toBind_3240_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_3279_,
                                        v___f_3260_,
                                    );
                                    return v___x_3280_;
                                } else {
                                    crate::leanh::lean_inc_n(v_ref_3259_, 2);
                                    crate::leanh::lean_inc(v___f_3246_);
                                    v___f_3281_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3281_, 0, v___f_3246_);
                                    crate::leanh::lean_closure_set(v___f_3281_, 1, v_ref_3259_);
                                    v___f_3282_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3282_, 0, v___f_3246_);
                                    crate::leanh::lean_closure_set(v___f_3282_, 1, v_ref_3259_);
                                    v___x_3283_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v_ns_3284_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3283_);
                                    v___x_3285_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___f_3286_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    crate::leanh::lean_closure_set(v___f_3286_, 0, v___x_3242_);
                                    crate::leanh::lean_closure_set(v___f_3286_, 1, v___x_3243_);
                                    crate::leanh::lean_closure_set(v___f_3286_, 2, v___x_3244_);
                                    crate::leanh::lean_closure_set(v___f_3286_, 3, v___x_3283_);
                                    crate::leanh::lean_closure_set(v___f_3286_, 4, v___x_3285_);
                                    v___x_3287_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3285_);
                                    crate::leanh::lean_dec(v_stx_3245_);
                                    v___x_3288_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13;
                                    v___x_3333_ = l_Lean_Syntax_getArgs(v___x_3287_);
                                    crate::leanh::lean_dec(v___x_3287_);
                                    v___x_3334_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14;
                                    v___x_3335_ = lean_array_get_size(v___x_3333_);
                                    v___x_3336_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                                    v___x_3337_ = lean_nat_dec_lt(v___x_3283_, v___x_3335_);
                                    if v___x_3337_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3333_);
                                        v___y_3290_ = v___x_3334_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3338_ =
                                            crate::leanh::lean_box((v___x_3272_) as usize);
                                        v___x_3339_ =
                                            crate::leanh::lean_box((v___x_3269_) as usize);
                                        v___f_3340_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed as *mut core::ffi::c_void, 4, 2);
                                        crate::leanh::lean_closure_set(v___f_3340_, 0, v___x_3338_);
                                        crate::leanh::lean_closure_set(v___f_3340_, 1, v___x_3339_);
                                        v___x_3341_ =
                                            crate::leanh::lean_box((v___x_3272_) as usize);
                                        v___x_3342_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
                                        crate::leanh::lean_ctor_set(v___x_3342_, 1, v___x_3334_);
                                        v___x_3343_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
                                        if v___x_3343_ == 0 {
                                            if v___x_3337_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3342_, 2);
                                                crate::leanh::lean_dec_ref(v___f_3340_);
                                                crate::leanh::lean_dec_ref(v___x_3333_);
                                                v___y_3290_ = v___x_3334_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3344_ = 0usize;
                                                v___x_3345_ = lean_usize_of_nat(v___x_3335_);
                                                v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3344_, v___x_3345_, v___x_3342_);
                                                v_snd_3347_ =
                                                    crate::leanh::lean_ctor_get(v___x_3346_, 1);
                                                crate::leanh::lean_inc(v_snd_3347_);
                                                crate::leanh::lean_dec(v___x_3346_);
                                                v___y_3290_ = v_snd_3347_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___x_3348_ = 0usize;
                                            v___x_3349_ = lean_usize_of_nat(v___x_3335_);
                                            v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3348_, v___x_3349_, v___x_3342_);
                                            v_snd_3351_ =
                                                crate::leanh::lean_ctor_get(v___x_3350_, 1);
                                            crate::leanh::lean_inc(v_snd_3351_);
                                            crate::leanh::lean_dec(v___x_3350_);
                                            v___y_3290_ = v_snd_3351_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___f_3251_);
                                crate::leanh::lean_dec_ref(v___f_3250_);
                                crate::leanh::lean_dec_ref(v___x_3244_);
                                crate::leanh::lean_dec_ref(v___x_3243_);
                                crate::leanh::lean_dec_ref(v___x_3242_);
                                crate::leanh::lean_inc(v_inst_3239_);
                                v___x_3352_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                    v_inst_3248_,
                                    v_inst_3239_,
                                );
                                v_getEnv_3353_ = crate::leanh::lean_ctor_get(v_inst_3249_, 0);
                                v_modifyEnv_3354_ = crate::leanh::lean_ctor_get(v_inst_3249_, 1);
                                v_isSharedCheck_3383_ =
                                    (!crate::leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                                if v_isSharedCheck_3383_ == 0 {
                                    v___x_3356_ = v_inst_3249_;
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_modifyEnv_3354_);
                                    crate::leanh::lean_inc(v_getEnv_3353_);
                                    crate::leanh::lean_dec(v_inst_3249_);
                                    v___x_3356_ = crate::leanh::lean_box(0);
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_3258_);
                            crate::leanh::lean_dec_ref(v___f_3251_);
                            crate::leanh::lean_dec_ref(v___f_3250_);
                            crate::leanh::lean_dec_ref(v___x_3244_);
                            crate::leanh::lean_dec_ref(v___x_3243_);
                            crate::leanh::lean_dec_ref(v___x_3242_);
                            crate::leanh::lean_inc(v_inst_3239_);
                            v___x_3384_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                v_inst_3248_,
                                v_inst_3239_,
                            );
                            v_getEnv_3385_ = crate::leanh::lean_ctor_get(v_inst_3249_, 0);
                            v_modifyEnv_3386_ = crate::leanh::lean_ctor_get(v_inst_3249_, 1);
                            v_isSharedCheck_3415_ =
                                (!crate::leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                            if v_isSharedCheck_3415_ == 0 {
                                v___x_3388_ = v_inst_3249_;
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_modifyEnv_3386_);
                                crate::leanh::lean_inc(v_getEnv_3385_);
                                crate::leanh::lean_dec(v_inst_3249_);
                                v___x_3388_ = crate::leanh::lean_box(0);
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_3258_);
                        crate::leanh::lean_dec(v_inst_3257_);
                        crate::leanh::lean_dec_ref(v_inst_3256_);
                        crate::leanh::lean_dec_ref(v_inst_3255_);
                        crate::leanh::lean_dec_ref(v___f_3251_);
                        crate::leanh::lean_dec_ref(v___f_3250_);
                        crate::leanh::lean_dec_ref(v___x_3244_);
                        crate::leanh::lean_dec_ref(v___x_3243_);
                        crate::leanh::lean_dec_ref(v___x_3242_);
                        crate::leanh::lean_inc(v_ref_3259_);
                        v___f_3416_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3416_, 0, v___f_3246_);
                        crate::leanh::lean_closure_set(v___f_3416_, 1, v_ref_3259_);
                        v___x_3417_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3418_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3417_);
                        crate::leanh::lean_dec(v_stx_3245_);
                        v_nss_3419_ = l_Lean_Syntax_getArgs(v___x_3418_);
                        crate::leanh::lean_dec(v___x_3418_);
                        v___x_3420_ = crate::leanh::lean_box(0);
                        v___f_3421_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3421_, 0, v___x_3420_);
                        crate::leanh::lean_closure_set(v___f_3421_, 1, v_toPure_3238_);
                        crate::leanh::lean_inc_ref(v___f_3421_);
                        crate::leanh::lean_inc_n(v_toBind_3240_, 2);
                        crate::leanh::lean_inc_ref(v___x_3254_);
                        v___f_3422_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed
                                as *mut core::ffi::c_void,
                            15,
                            11,
                        );
                        crate::leanh::lean_closure_set(v___f_3422_, 0, v_inst_3248_);
                        crate::leanh::lean_closure_set(v___f_3422_, 1, v_inst_3239_);
                        crate::leanh::lean_closure_set(v___f_3422_, 2, v_inst_3249_);
                        crate::leanh::lean_closure_set(v___f_3422_, 3, v___x_3254_);
                        crate::leanh::lean_closure_set(v___f_3422_, 4, v_toBind_3240_);
                        crate::leanh::lean_closure_set(v___f_3422_, 5, v___f_3421_);
                        crate::leanh::lean_closure_set(v___f_3422_, 6, v___x_3420_);
                        crate::leanh::lean_closure_set(v___f_3422_, 7, v___f_3421_);
                        crate::leanh::lean_closure_set(v___f_3422_, 8, v_inst_3247_);
                        crate::leanh::lean_closure_set(v___f_3422_, 9, v_inst_3252_);
                        crate::leanh::lean_closure_set(v___f_3422_, 10, v_inst_3253_);
                        v_sz_3423_ = lean_array_size(v_nss_3419_);
                        v___x_3424_ = 0usize;
                        v___x_7255__overap_3425_ =
                            l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3254_,
                                v_nss_3419_,
                                v___f_3422_,
                                v_sz_3423_,
                                v___x_3424_,
                                v___x_3420_,
                            );
                        v___x_3426_ =
                            crate::leanh::lean_apply_1(v___x_7255__overap_3425_, v_ref_3259_);
                        v___x_3427_ = crate::leanh::lean_apply_4(
                            v_toBind_3240_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3426_,
                            v___f_3416_,
                        );
                        v___x_3428_ = crate::leanh::lean_apply_4(
                            v_toBind_3240_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3427_,
                            v___f_3260_,
                        );
                        return v___x_3428_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3258_);
                    crate::leanh::lean_dec(v_inst_3257_);
                    crate::leanh::lean_dec_ref(v_inst_3256_);
                    crate::leanh::lean_dec_ref(v_inst_3255_);
                    crate::leanh::lean_dec_ref(v___f_3251_);
                    crate::leanh::lean_dec_ref(v___f_3250_);
                    crate::leanh::lean_dec_ref(v___x_3244_);
                    crate::leanh::lean_dec_ref(v___x_3243_);
                    crate::leanh::lean_dec_ref(v___x_3242_);
                    crate::leanh::lean_inc(v_ref_3259_);
                    v___f_3429_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3429_, 0, v___f_3246_);
                    crate::leanh::lean_closure_set(v___f_3429_, 1, v_ref_3259_);
                    v___x_3430_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3431_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3430_);
                    crate::leanh::lean_dec(v_stx_3245_);
                    v___x_3432_ = crate::leanh::lean_box(0);
                    v_nss_3433_ = l_Lean_Syntax_getArgs(v___x_3431_);
                    crate::leanh::lean_dec(v___x_3431_);
                    v___x_3434_ = crate::leanh::lean_box(0);
                    v___f_3435_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3435_, 0, v___x_3434_);
                    crate::leanh::lean_closure_set(v___f_3435_, 1, v_toPure_3238_);
                    crate::leanh::lean_inc_ref(v___f_3435_);
                    crate::leanh::lean_inc_n(v_toBind_3240_, 2);
                    crate::leanh::lean_inc_ref(v___x_3254_);
                    v___f_3436_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed
                            as *mut core::ffi::c_void,
                        16,
                        12,
                    );
                    crate::leanh::lean_closure_set(v___f_3436_, 0, v_inst_3248_);
                    crate::leanh::lean_closure_set(v___f_3436_, 1, v_inst_3239_);
                    crate::leanh::lean_closure_set(v___f_3436_, 2, v_inst_3249_);
                    crate::leanh::lean_closure_set(v___f_3436_, 3, v___x_3254_);
                    crate::leanh::lean_closure_set(v___f_3436_, 4, v_toBind_3240_);
                    crate::leanh::lean_closure_set(v___f_3436_, 5, v___f_3435_);
                    crate::leanh::lean_closure_set(v___f_3436_, 6, v___x_3432_);
                    crate::leanh::lean_closure_set(v___f_3436_, 7, v___x_3434_);
                    crate::leanh::lean_closure_set(v___f_3436_, 8, v___f_3435_);
                    crate::leanh::lean_closure_set(v___f_3436_, 9, v_inst_3247_);
                    crate::leanh::lean_closure_set(v___f_3436_, 10, v_inst_3252_);
                    crate::leanh::lean_closure_set(v___f_3436_, 11, v_inst_3253_);
                    v_sz_3437_ = lean_array_size(v_nss_3433_);
                    v___x_3438_ = 0usize;
                    v___x_7267__overap_3439_ =
                        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3254_,
                            v_nss_3433_,
                            v___f_3436_,
                            v_sz_3437_,
                            v___x_3438_,
                            v___x_3434_,
                        );
                    v___x_3440_ = crate::leanh::lean_apply_1(v___x_7267__overap_3439_, v_ref_3259_);
                    v___x_3441_ = crate::leanh::lean_apply_4(
                        v_toBind_3240_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3440_,
                        v___f_3429_,
                    );
                    v___x_3442_ = crate::leanh::lean_apply_4(
                        v_toBind_3240_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3441_,
                        v___f_3260_,
                    );
                    return v___x_3442_;
                }
            }
            1 => {
                v_sz_3291_ = lean_array_size(v___y_3290_);
                v___x_3292_ = 0usize;
                v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3288_,
                    v___f_3286_,
                    v_sz_3291_,
                    v___x_3292_,
                    v___y_3290_,
                );
                if crate::leanh::lean_obj_tag(v___x_3293_) == 0 {
                    crate::leanh::lean_dec(v_ns_3284_);
                    crate::leanh::lean_dec_ref(v___f_3281_);
                    crate::leanh::lean_dec(v_inst_3257_);
                    crate::leanh::lean_dec_ref(v_inst_3256_);
                    crate::leanh::lean_dec_ref(v_inst_3255_);
                    crate::leanh::lean_dec_ref(v___x_3254_);
                    crate::leanh::lean_dec(v_inst_3253_);
                    crate::leanh::lean_dec_ref(v_inst_3252_);
                    crate::leanh::lean_dec_ref(v___f_3251_);
                    crate::leanh::lean_dec_ref(v___f_3250_);
                    crate::leanh::lean_dec_ref(v_inst_3249_);
                    crate::leanh::lean_dec_ref(v_inst_3248_);
                    crate::leanh::lean_dec(v_inst_3239_);
                    crate::leanh::lean_dec(v_toPure_3238_);
                    crate::leanh::lean_inc_ref(v_inst_3247_);
                    v___f_3294_ = crate::leanh::lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3294_, 0, v_inst_3247_);
                    v___f_3295_ = crate::leanh::lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3295_, 0, v_inst_3247_);
                    v___x_3296_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___f_3294_);
                    crate::leanh::lean_ctor_set(v___x_3296_, 1, v___f_3295_);
                    v___x_7151__overap_3297_ =
                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3296_);
                    v___x_3298_ = crate::leanh::lean_apply_1(v___x_7151__overap_3297_, v_ref_3259_);
                    crate::leanh::lean_inc(v_toBind_3240_);
                    v___x_3299_ = crate::leanh::lean_apply_4(
                        v_toBind_3240_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3298_,
                        v___f_3282_,
                    );
                    v___x_3300_ = crate::leanh::lean_apply_4(
                        v_toBind_3240_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3299_,
                        v___f_3260_,
                    );
                    return v___x_3300_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_3282_);
                    v_val_3301_ = crate::leanh::lean_ctor_get(v___x_3293_, 0);
                    crate::leanh::lean_inc(v_val_3301_);
                    crate::leanh::lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3302_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_sz_3303_ = lean_array_size(v_val_3301_);
                    crate::leanh::lean_inc(v_inst_3239_);
                    v___x_3304_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                        v_inst_3248_,
                        v_inst_3239_,
                    );
                    v_getEnv_3305_ = crate::leanh::lean_ctor_get(v_inst_3249_, 0);
                    v_modifyEnv_3306_ = crate::leanh::lean_ctor_get(v_inst_3249_, 1);
                    v_isSharedCheck_3332_ = (!crate::leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3308_ = v_inst_3249_;
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_modifyEnv_3306_);
                        crate::leanh::lean_inc(v_getEnv_3305_);
                        crate::leanh::lean_dec(v_inst_3249_);
                        v___x_3308_ = crate::leanh::lean_box(0);
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_val_3301_);
                v_tos_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3302_,
                    v___f_3250_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v_froms_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3302_,
                    v___f_3251_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v___x_3312_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3313_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3313_, 0, v_modifyEnv_3306_);
                crate::leanh::lean_closure_set(v___f_3313_, 1, v___x_3312_);
                v___x_3314_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3314_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3314_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3314_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3314_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3314_, 4, v_getEnv_3305_);
                if v_isShared_3309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3308_, 1, v___f_3313_);
                    crate::leanh::lean_ctor_set(v___x_3308_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3308_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___f_3313_);
                    v___x_3316_ = v_reuseFailAlloc_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_inst_3247_);
                v___f_3317_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3317_, 0, v_inst_3247_);
                v___f_3318_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3318_, 0, v_inst_3247_);
                v___x_3319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3319_, 0, v___f_3317_);
                crate::leanh::lean_ctor_set(v___x_3319_, 1, v___f_3318_);
                v___x_3320_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3321_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3312_,
                    v___x_3320_,
                    v_inst_3252_,
                );
                v___f_3322_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3322_, 0, v_inst_3253_);
                crate::leanh::lean_closure_set(v___f_3322_, 1, v___x_3312_);
                crate::leanh::lean_inc_ref_n(v___x_3254_, 2);
                crate::leanh::lean_inc_ref(v___f_3322_);
                v___x_3323_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3322_,
                    v___x_3254_,
                );
                crate::leanh::lean_inc(v___x_3323_);
                crate::leanh::lean_inc_ref(v___x_3321_);
                crate::leanh::lean_inc_ref(v___x_3319_);
                v___x_3324_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3324_, 0, v___x_3319_);
                crate::leanh::lean_ctor_set(v___x_3324_, 1, v___x_3321_);
                crate::leanh::lean_ctor_set(v___x_3324_, 2, v___x_3323_);
                v___x_3325_ =
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1;
                crate::leanh::lean_inc(v_ref_3259_);
                crate::leanh::lean_inc_ref(v___x_3304_);
                crate::leanh::lean_inc_ref(v___x_3324_);
                crate::leanh::lean_inc_ref(v___x_3316_);
                crate::leanh::lean_inc_n(v_toBind_3240_, 2);
                v___f_3326_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed
                        as *mut core::ffi::c_void,
                    21,
                    20,
                );
                crate::leanh::lean_closure_set(v___f_3326_, 0, v_froms_3311_);
                crate::leanh::lean_closure_set(v___f_3326_, 1, v_tos_3310_);
                crate::leanh::lean_closure_set(v___f_3326_, 2, v_toPure_3238_);
                crate::leanh::lean_closure_set(v___f_3326_, 3, v___x_3312_);
                crate::leanh::lean_closure_set(v___f_3326_, 4, v_inst_3255_);
                crate::leanh::lean_closure_set(v___f_3326_, 5, v_inst_3239_);
                crate::leanh::lean_closure_set(v___f_3326_, 6, v_toBind_3240_);
                crate::leanh::lean_closure_set(v___f_3326_, 7, v___x_3254_);
                crate::leanh::lean_closure_set(v___f_3326_, 8, v___x_3316_);
                crate::leanh::lean_closure_set(v___f_3326_, 9, v___x_3324_);
                crate::leanh::lean_closure_set(v___f_3326_, 10, v_inst_3256_);
                crate::leanh::lean_closure_set(v___f_3326_, 11, v_inst_3257_);
                crate::leanh::lean_closure_set(v___f_3326_, 12, v___x_3319_);
                crate::leanh::lean_closure_set(v___f_3326_, 13, v___x_3321_);
                crate::leanh::lean_closure_set(v___f_3326_, 14, v___x_3323_);
                crate::leanh::lean_closure_set(v___f_3326_, 15, v___f_3322_);
                crate::leanh::lean_closure_set(v___f_3326_, 16, v___x_3304_);
                crate::leanh::lean_closure_set(v___f_3326_, 17, v___x_3325_);
                crate::leanh::lean_closure_set(v___f_3326_, 18, v_ref_3259_);
                crate::leanh::lean_closure_set(v___f_3326_, 19, v___f_3281_);
                v___x_7179__overap_3327_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3304_,
                    v___x_3316_,
                    v___x_3324_,
                    v_ns_3284_,
                );
                v___x_3328_ = crate::leanh::lean_apply_1(v___x_7179__overap_3327_, v_ref_3259_);
                v___x_3329_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3328_,
                    v___f_3326_,
                );
                v___x_3330_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3329_,
                    v___f_3260_,
                );
                return v___x_3330_;
            }
            4 => {
                crate::leanh::lean_inc(v_ref_3259_);
                v___f_3358_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3358_, 0, v___f_3246_);
                crate::leanh::lean_closure_set(v___f_3358_, 1, v_ref_3259_);
                v___x_3359_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ns_3360_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3359_);
                v___x_3361_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3362_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3361_);
                crate::leanh::lean_dec(v_stx_3245_);
                v_ids_3363_ = l_Lean_Syntax_getArgs(v___x_3362_);
                crate::leanh::lean_dec(v___x_3362_);
                v___x_3364_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3365_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3365_, 0, v_modifyEnv_3354_);
                crate::leanh::lean_closure_set(v___f_3365_, 1, v___x_3364_);
                v___x_3366_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3366_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3366_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3366_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3366_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3366_, 4, v_getEnv_3353_);
                if v_isShared_3357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3356_, 1, v___f_3365_);
                    crate::leanh::lean_ctor_set(v___x_3356_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3356_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___f_3365_);
                    v___x_3368_ = v_reuseFailAlloc_3382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_inst_3247_);
                v___f_3369_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3369_, 0, v_inst_3247_);
                v___f_3370_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3370_, 0, v_inst_3247_);
                v___x_3371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3371_, 0, v___f_3369_);
                crate::leanh::lean_ctor_set(v___x_3371_, 1, v___f_3370_);
                v___x_3372_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3373_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3364_,
                    v___x_3372_,
                    v_inst_3252_,
                );
                v___f_3374_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3374_, 0, v_inst_3253_);
                crate::leanh::lean_closure_set(v___f_3374_, 1, v___x_3364_);
                crate::leanh::lean_inc_ref_n(v___x_3254_, 2);
                crate::leanh::lean_inc_ref(v___f_3374_);
                v___x_3375_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3374_,
                    v___x_3254_,
                );
                crate::leanh::lean_inc(v___x_3375_);
                crate::leanh::lean_inc_ref(v___x_3373_);
                crate::leanh::lean_inc_ref(v___x_3371_);
                v___x_3376_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3376_, 0, v___x_3371_);
                crate::leanh::lean_ctor_set(v___x_3376_, 1, v___x_3373_);
                crate::leanh::lean_ctor_set(v___x_3376_, 2, v___x_3375_);
                crate::leanh::lean_inc_ref(v___x_3352_);
                crate::leanh::lean_inc_ref(v___x_3376_);
                crate::leanh::lean_inc_ref(v___x_3368_);
                crate::leanh::lean_inc_n(v_toBind_3240_, 2);
                crate::leanh::lean_inc(v_ref_3259_);
                v___f_3377_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed
                        as *mut core::ffi::c_void,
                    20,
                    19,
                );
                crate::leanh::lean_closure_set(v___f_3377_, 0, v_ids_3363_);
                crate::leanh::lean_closure_set(v___f_3377_, 1, v___f_3258_);
                crate::leanh::lean_closure_set(v___f_3377_, 2, v_inst_3239_);
                crate::leanh::lean_closure_set(v___f_3377_, 3, v_ref_3259_);
                crate::leanh::lean_closure_set(v___f_3377_, 4, v_toBind_3240_);
                crate::leanh::lean_closure_set(v___f_3377_, 5, v___f_3358_);
                crate::leanh::lean_closure_set(v___f_3377_, 6, v_toPure_3238_);
                crate::leanh::lean_closure_set(v___f_3377_, 7, v___x_3364_);
                crate::leanh::lean_closure_set(v___f_3377_, 8, v_inst_3255_);
                crate::leanh::lean_closure_set(v___f_3377_, 9, v___x_3254_);
                crate::leanh::lean_closure_set(v___f_3377_, 10, v___x_3368_);
                crate::leanh::lean_closure_set(v___f_3377_, 11, v___x_3376_);
                crate::leanh::lean_closure_set(v___f_3377_, 12, v_inst_3256_);
                crate::leanh::lean_closure_set(v___f_3377_, 13, v_inst_3257_);
                crate::leanh::lean_closure_set(v___f_3377_, 14, v___x_3371_);
                crate::leanh::lean_closure_set(v___f_3377_, 15, v___x_3373_);
                crate::leanh::lean_closure_set(v___f_3377_, 16, v___x_3375_);
                crate::leanh::lean_closure_set(v___f_3377_, 17, v___f_3374_);
                crate::leanh::lean_closure_set(v___f_3377_, 18, v___x_3352_);
                v___x_7223__overap_3378_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3352_,
                    v___x_3368_,
                    v___x_3376_,
                    v_ns_3360_,
                );
                v___x_3379_ = crate::leanh::lean_apply_1(v___x_7223__overap_3378_, v_ref_3259_);
                v___x_3380_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3379_,
                    v___f_3377_,
                );
                v___x_3381_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3380_,
                    v___f_3260_,
                );
                return v___x_3381_;
            }
            6 => {
                crate::leanh::lean_inc(v_ref_3259_);
                v___f_3390_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3390_, 0, v___f_3246_);
                crate::leanh::lean_closure_set(v___f_3390_, 1, v_ref_3259_);
                v___x_3391_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ns_3392_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3391_);
                v___x_3393_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3394_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3393_);
                crate::leanh::lean_dec(v_stx_3245_);
                v_ids_3395_ = l_Lean_Syntax_getArgs(v___x_3394_);
                crate::leanh::lean_dec(v___x_3394_);
                v___x_3396_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3397_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3397_, 0, v_modifyEnv_3386_);
                crate::leanh::lean_closure_set(v___f_3397_, 1, v___x_3396_);
                v___x_3398_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3398_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3398_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3398_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3398_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3398_, 4, v_getEnv_3385_);
                if v_isShared_3389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3388_, 1, v___f_3397_);
                    crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3398_);
                    v___x_3400_ = v___x_3388_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___f_3397_);
                    v___x_3400_ = v_reuseFailAlloc_3414_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v_inst_3247_);
                v___f_3401_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3401_, 0, v_inst_3247_);
                v___f_3402_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3402_, 0, v_inst_3247_);
                v___x_3403_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3403_, 0, v___f_3401_);
                crate::leanh::lean_ctor_set(v___x_3403_, 1, v___f_3402_);
                v___x_3404_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3405_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3396_,
                    v___x_3404_,
                    v_inst_3252_,
                );
                v___f_3406_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3406_, 0, v_inst_3253_);
                crate::leanh::lean_closure_set(v___f_3406_, 1, v___x_3396_);
                crate::leanh::lean_inc_ref_n(v___x_3254_, 2);
                crate::leanh::lean_inc_ref(v___f_3406_);
                v___x_3407_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3406_,
                    v___x_3254_,
                );
                crate::leanh::lean_inc(v___x_3407_);
                crate::leanh::lean_inc_ref(v___x_3405_);
                crate::leanh::lean_inc_ref(v___x_3403_);
                v___x_3408_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3408_, 0, v___x_3403_);
                crate::leanh::lean_ctor_set(v___x_3408_, 1, v___x_3405_);
                crate::leanh::lean_ctor_set(v___x_3408_, 2, v___x_3407_);
                crate::leanh::lean_inc(v_ref_3259_);
                crate::leanh::lean_inc_ref(v___x_3384_);
                crate::leanh::lean_inc_ref(v___x_3408_);
                crate::leanh::lean_inc_ref(v___x_3400_);
                crate::leanh::lean_inc_n(v_toBind_3240_, 2);
                v___f_3409_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed
                        as *mut core::ffi::c_void,
                    19,
                    18,
                );
                crate::leanh::lean_closure_set(v___f_3409_, 0, v_toPure_3238_);
                crate::leanh::lean_closure_set(v___f_3409_, 1, v___x_3396_);
                crate::leanh::lean_closure_set(v___f_3409_, 2, v_inst_3255_);
                crate::leanh::lean_closure_set(v___f_3409_, 3, v_inst_3239_);
                crate::leanh::lean_closure_set(v___f_3409_, 4, v_toBind_3240_);
                crate::leanh::lean_closure_set(v___f_3409_, 5, v___x_3254_);
                crate::leanh::lean_closure_set(v___f_3409_, 6, v___x_3400_);
                crate::leanh::lean_closure_set(v___f_3409_, 7, v___x_3408_);
                crate::leanh::lean_closure_set(v___f_3409_, 8, v_inst_3256_);
                crate::leanh::lean_closure_set(v___f_3409_, 9, v_inst_3257_);
                crate::leanh::lean_closure_set(v___f_3409_, 10, v___x_3403_);
                crate::leanh::lean_closure_set(v___f_3409_, 11, v___x_3405_);
                crate::leanh::lean_closure_set(v___f_3409_, 12, v___x_3407_);
                crate::leanh::lean_closure_set(v___f_3409_, 13, v___f_3406_);
                crate::leanh::lean_closure_set(v___f_3409_, 14, v___x_3384_);
                crate::leanh::lean_closure_set(v___f_3409_, 15, v_ids_3395_);
                crate::leanh::lean_closure_set(v___f_3409_, 16, v_ref_3259_);
                crate::leanh::lean_closure_set(v___f_3409_, 17, v___f_3390_);
                v___x_7244__overap_3410_ = l_Lean_resolveNamespace___redArg(
                    v___x_3254_,
                    v___x_3384_,
                    v___x_3400_,
                    v___x_3408_,
                    v_ns_3392_,
                );
                v___x_3411_ = crate::leanh::lean_apply_1(v___x_7244__overap_3410_, v_ref_3259_);
                v___x_3412_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3411_,
                    v___f_3409_,
                );
                v___x_3413_ = crate::leanh::lean_apply_4(
                    v_toBind_3240_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3412_,
                    v___f_3260_,
                );
                return v___x_3413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3443_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_3444_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_toBind_3445_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3446_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3447_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3448_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3449_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_stx_3450_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_3451_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_3452_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_3453_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_3454_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___f_3455_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_3456_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_3457_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_3458_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_3459_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_3460_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_inst_3461_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_inst_3462_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___f_3463_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_ref_3464_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___x_8610__boxed_3465_: u8 = 0;
    let mut v_res_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8610__boxed_3465_ = (crate::leanh::lean_unbox(v___x_3446_) as u8);
    v_res_3466_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(
        v_toPure_3443_,
        v_inst_3444_,
        v_toBind_3445_,
        v___x_8610__boxed_3465_,
        v___x_3447_,
        v___x_3448_,
        v___x_3449_,
        v_stx_3450_,
        v___f_3451_,
        v_inst_3452_,
        v_inst_3453_,
        v_inst_3454_,
        v___f_3455_,
        v___f_3456_,
        v_inst_3457_,
        v_inst_3458_,
        v___x_3459_,
        v_inst_3460_,
        v_inst_3461_,
        v_inst_3462_,
        v___f_3463_,
        v_ref_3464_,
    );
    return v_res_3466_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(
    mut v_toPure_3467_: *mut crate::leanh::LeanObject,
    mut v_____x_3468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3469_ = crate::leanh::lean_ctor_get(v_____x_3468_, 0);
    crate::leanh::lean_inc(v_fst_3469_);
    crate::leanh::lean_dec_ref(v_____x_3468_);
    v___x_3470_ =
        crate::leanh::lean_apply_2(v_toPure_3467_, crate::leanh::lean_box(0), v_fst_3469_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(
    mut v_toApplicative_3480_: *mut crate::leanh::LeanObject,
    mut v_stx_3481_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3482_: *mut crate::leanh::LeanObject,
    mut v_inst_3483_: *mut crate::leanh::LeanObject,
    mut v_toBind_3484_: *mut crate::leanh::LeanObject,
    mut v___f_3485_: *mut crate::leanh::LeanObject,
    mut v_inst_3486_: *mut crate::leanh::LeanObject,
    mut v_inst_3487_: *mut crate::leanh::LeanObject,
    mut v_inst_3488_: *mut crate::leanh::LeanObject,
    mut v___f_3489_: *mut crate::leanh::LeanObject,
    mut v___f_3490_: *mut crate::leanh::LeanObject,
    mut v_inst_3491_: *mut crate::leanh::LeanObject,
    mut v_inst_3492_: *mut crate::leanh::LeanObject,
    mut v___x_3493_: *mut crate::leanh::LeanObject,
    mut v_inst_3494_: *mut crate::leanh::LeanObject,
    mut v_inst_3495_: *mut crate::leanh::LeanObject,
    mut v_inst_3496_: *mut crate::leanh::LeanObject,
    mut v___f_3497_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3499_ = crate::leanh::lean_ctor_get(v_toApplicative_3480_, 1);
    crate::leanh::lean_inc_n(v_toPure_3499_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3480_);
    v___x_3500_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0;
    v___x_3501_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1;
    v___x_3502_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2;
    v___x_3503_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4;
    crate::leanh::lean_inc(v_stx_3481_);
    v___x_3504_ = l_Lean_Syntax_isOfKind(v_stx_3481_, v___x_3503_);
    v___x_3505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3505_, 0, v_____do__lift_3482_);
    crate::leanh::lean_ctor_set(v___x_3505_, 1, v_____do__lift_3498_);
    v___x_3506_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3506_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3506_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3506_, 2, v___x_3505_);
    crate::leanh::lean_inc(v_inst_3483_);
    v___x_3507_ = crate::leanh::lean_apply_2(v_inst_3483_, crate::leanh::lean_box(0), v___x_3506_);
    v___x_3508_ = crate::leanh::lean_box((v___x_3504_) as usize);
    crate::leanh::lean_inc_n(v_toBind_3484_, 2);
    v___f_3509_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed as *mut core::ffi::c_void,
        22,
        21,
    );
    crate::leanh::lean_closure_set(v___f_3509_, 0, v_toPure_3499_);
    crate::leanh::lean_closure_set(v___f_3509_, 1, v_inst_3483_);
    crate::leanh::lean_closure_set(v___f_3509_, 2, v_toBind_3484_);
    crate::leanh::lean_closure_set(v___f_3509_, 3, v___x_3508_);
    crate::leanh::lean_closure_set(v___f_3509_, 4, v___x_3500_);
    crate::leanh::lean_closure_set(v___f_3509_, 5, v___x_3501_);
    crate::leanh::lean_closure_set(v___f_3509_, 6, v___x_3502_);
    crate::leanh::lean_closure_set(v___f_3509_, 7, v_stx_3481_);
    crate::leanh::lean_closure_set(v___f_3509_, 8, v___f_3485_);
    crate::leanh::lean_closure_set(v___f_3509_, 9, v_inst_3486_);
    crate::leanh::lean_closure_set(v___f_3509_, 10, v_inst_3487_);
    crate::leanh::lean_closure_set(v___f_3509_, 11, v_inst_3488_);
    crate::leanh::lean_closure_set(v___f_3509_, 12, v___f_3489_);
    crate::leanh::lean_closure_set(v___f_3509_, 13, v___f_3490_);
    crate::leanh::lean_closure_set(v___f_3509_, 14, v_inst_3491_);
    crate::leanh::lean_closure_set(v___f_3509_, 15, v_inst_3492_);
    crate::leanh::lean_closure_set(v___f_3509_, 16, v___x_3493_);
    crate::leanh::lean_closure_set(v___f_3509_, 17, v_inst_3494_);
    crate::leanh::lean_closure_set(v___f_3509_, 18, v_inst_3495_);
    crate::leanh::lean_closure_set(v___f_3509_, 19, v_inst_3496_);
    crate::leanh::lean_closure_set(v___f_3509_, 20, v___f_3497_);
    v___f_3510_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3510_, 0, v_toPure_3499_);
    v___x_3511_ = crate::leanh::lean_apply_4(
        v_toBind_3484_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3507_,
        v___f_3509_,
    );
    v___x_3512_ = crate::leanh::lean_apply_4(
        v_toBind_3484_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3511_,
        v___f_3510_,
    );
    return v___x_3512_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3513_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_stx_3514_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_3515_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_3516_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toBind_3517_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_3518_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_3519_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_3520_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_3521_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_3522_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___f_3523_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_3524_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_3525_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_3526_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_3527_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_3528_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_3529_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_3530_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_3531_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3532_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(
        v_toApplicative_3513_,
        v_stx_3514_,
        v_____do__lift_3515_,
        v_inst_3516_,
        v_toBind_3517_,
        v___f_3518_,
        v_inst_3519_,
        v_inst_3520_,
        v_inst_3521_,
        v___f_3522_,
        v___f_3523_,
        v_inst_3524_,
        v_inst_3525_,
        v___x_3526_,
        v_inst_3527_,
        v_inst_3528_,
        v_inst_3529_,
        v___f_3530_,
        v_____do__lift_3531_,
    );
    return v_res_3532_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(
    mut v_toApplicative_3533_: *mut crate::leanh::LeanObject,
    mut v_stx_3534_: *mut crate::leanh::LeanObject,
    mut v_inst_3535_: *mut crate::leanh::LeanObject,
    mut v_toBind_3536_: *mut crate::leanh::LeanObject,
    mut v___f_3537_: *mut crate::leanh::LeanObject,
    mut v_inst_3538_: *mut crate::leanh::LeanObject,
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_inst_3540_: *mut crate::leanh::LeanObject,
    mut v___f_3541_: *mut crate::leanh::LeanObject,
    mut v___f_3542_: *mut crate::leanh::LeanObject,
    mut v_inst_3543_: *mut crate::leanh::LeanObject,
    mut v_inst_3544_: *mut crate::leanh::LeanObject,
    mut v___x_3545_: *mut crate::leanh::LeanObject,
    mut v_inst_3546_: *mut crate::leanh::LeanObject,
    mut v_inst_3547_: *mut crate::leanh::LeanObject,
    mut v_inst_3548_: *mut crate::leanh::LeanObject,
    mut v___f_3549_: *mut crate::leanh::LeanObject,
    mut v_getCurrNamespace_3550_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_3536_);
    v___f_3552_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    crate::leanh::lean_closure_set(v___f_3552_, 0, v_toApplicative_3533_);
    crate::leanh::lean_closure_set(v___f_3552_, 1, v_stx_3534_);
    crate::leanh::lean_closure_set(v___f_3552_, 2, v_____do__lift_3551_);
    crate::leanh::lean_closure_set(v___f_3552_, 3, v_inst_3535_);
    crate::leanh::lean_closure_set(v___f_3552_, 4, v_toBind_3536_);
    crate::leanh::lean_closure_set(v___f_3552_, 5, v___f_3537_);
    crate::leanh::lean_closure_set(v___f_3552_, 6, v_inst_3538_);
    crate::leanh::lean_closure_set(v___f_3552_, 7, v_inst_3539_);
    crate::leanh::lean_closure_set(v___f_3552_, 8, v_inst_3540_);
    crate::leanh::lean_closure_set(v___f_3552_, 9, v___f_3541_);
    crate::leanh::lean_closure_set(v___f_3552_, 10, v___f_3542_);
    crate::leanh::lean_closure_set(v___f_3552_, 11, v_inst_3543_);
    crate::leanh::lean_closure_set(v___f_3552_, 12, v_inst_3544_);
    crate::leanh::lean_closure_set(v___f_3552_, 13, v___x_3545_);
    crate::leanh::lean_closure_set(v___f_3552_, 14, v_inst_3546_);
    crate::leanh::lean_closure_set(v___f_3552_, 15, v_inst_3547_);
    crate::leanh::lean_closure_set(v___f_3552_, 16, v_inst_3548_);
    crate::leanh::lean_closure_set(v___f_3552_, 17, v___f_3549_);
    v___x_3553_ = crate::leanh::lean_apply_4(
        v_toBind_3536_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_3550_,
        v___f_3552_,
    );
    return v___x_3553_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3554_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_stx_3555_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_3556_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toBind_3557_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_3558_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_3559_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_3560_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_3561_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_3562_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_3563_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_3564_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_3565_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_3566_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_3567_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_3568_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_3569_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_3570_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_getCurrNamespace_3571_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_3572_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3573_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(
        v_toApplicative_3554_,
        v_stx_3555_,
        v_inst_3556_,
        v_toBind_3557_,
        v___f_3558_,
        v_inst_3559_,
        v_inst_3560_,
        v_inst_3561_,
        v___f_3562_,
        v___f_3563_,
        v_inst_3564_,
        v_inst_3565_,
        v___x_3566_,
        v_inst_3567_,
        v_inst_3568_,
        v_inst_3569_,
        v___f_3570_,
        v_getCurrNamespace_3571_,
        v_____do__lift_3572_,
    );
    return v_res_3573_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(
    mut v_inst_3577_: *mut crate::leanh::LeanObject,
    mut v_inst_3578_: *mut crate::leanh::LeanObject,
    mut v_inst_3579_: *mut crate::leanh::LeanObject,
    mut v_inst_3580_: *mut crate::leanh::LeanObject,
    mut v_inst_3581_: *mut crate::leanh::LeanObject,
    mut v_inst_3582_: *mut crate::leanh::LeanObject,
    mut v_inst_3583_: *mut crate::leanh::LeanObject,
    mut v_inst_3584_: *mut crate::leanh::LeanObject,
    mut v_inst_3585_: *mut crate::leanh::LeanObject,
    mut v_inst_3586_: *mut crate::leanh::LeanObject,
    mut v_stx_3587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3588_ = crate::leanh::lean_ctor_get(v_inst_3577_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_3588_, 2);
    v_toBind_3589_ = crate::leanh::lean_ctor_get(v_inst_3577_, 1);
    crate::leanh::lean_inc_n(v_toBind_3589_, 3);
    v_getCurrNamespace_3590_ = crate::leanh::lean_ctor_get(v_inst_3585_, 0);
    crate::leanh::lean_inc(v_getCurrNamespace_3590_);
    v_getOpenDecls_3591_ = crate::leanh::lean_ctor_get(v_inst_3585_, 1);
    crate::leanh::lean_inc(v_getOpenDecls_3591_);
    crate::leanh::lean_dec_ref(v_inst_3585_);
    v___f_3592_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3592_, 0, v_toApplicative_3588_);
    crate::leanh::lean_inc(v_inst_3582_);
    v___f_3593_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3593_, 0, v_inst_3582_);
    crate::leanh::lean_closure_set(v___f_3593_, 1, v_toBind_3589_);
    crate::leanh::lean_closure_set(v___f_3593_, 2, v___f_3592_);
    v___f_3594_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0;
    v___f_3595_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1;
    v___f_3596_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2;
    crate::leanh::lean_inc_ref(v_inst_3577_);
    v___x_3597_ = l_StateRefT_x27_instMonad___redArg(v_inst_3577_);
    v___f_3598_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    crate::leanh::lean_closure_set(v___f_3598_, 0, v_toApplicative_3588_);
    crate::leanh::lean_closure_set(v___f_3598_, 1, v_stx_3587_);
    crate::leanh::lean_closure_set(v___f_3598_, 2, v_inst_3582_);
    crate::leanh::lean_closure_set(v___f_3598_, 3, v_toBind_3589_);
    crate::leanh::lean_closure_set(v___f_3598_, 4, v___f_3593_);
    crate::leanh::lean_closure_set(v___f_3598_, 5, v_inst_3579_);
    crate::leanh::lean_closure_set(v___f_3598_, 6, v_inst_3577_);
    crate::leanh::lean_closure_set(v___f_3598_, 7, v_inst_3578_);
    crate::leanh::lean_closure_set(v___f_3598_, 8, v___f_3594_);
    crate::leanh::lean_closure_set(v___f_3598_, 9, v___f_3595_);
    crate::leanh::lean_closure_set(v___f_3598_, 10, v_inst_3580_);
    crate::leanh::lean_closure_set(v___f_3598_, 11, v_inst_3581_);
    crate::leanh::lean_closure_set(v___f_3598_, 12, v___x_3597_);
    crate::leanh::lean_closure_set(v___f_3598_, 13, v_inst_3586_);
    crate::leanh::lean_closure_set(v___f_3598_, 14, v_inst_3583_);
    crate::leanh::lean_closure_set(v___f_3598_, 15, v_inst_3584_);
    crate::leanh::lean_closure_set(v___f_3598_, 16, v___f_3596_);
    crate::leanh::lean_closure_set(v___f_3598_, 17, v_getCurrNamespace_3590_);
    v___x_3599_ = crate::leanh::lean_apply_4(
        v_toBind_3589_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getOpenDecls_3591_,
        v___f_3598_,
    );
    return v___x_3599_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl(
    mut v_m_3600_: *mut crate::leanh::LeanObject,
    mut v_inst_3601_: *mut crate::leanh::LeanObject,
    mut v_inst_3602_: *mut crate::leanh::LeanObject,
    mut v_inst_3603_: *mut crate::leanh::LeanObject,
    mut v_inst_3604_: *mut crate::leanh::LeanObject,
    mut v_inst_3605_: *mut crate::leanh::LeanObject,
    mut v_inst_3606_: *mut crate::leanh::LeanObject,
    mut v_inst_3607_: *mut crate::leanh::LeanObject,
    mut v_inst_3608_: *mut crate::leanh::LeanObject,
    mut v_inst_3609_: *mut crate::leanh::LeanObject,
    mut v_inst_3610_: *mut crate::leanh::LeanObject,
    mut v_stx_3611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(
        v_inst_3601_,
        v_inst_3602_,
        v_inst_3603_,
        v_inst_3604_,
        v_inst_3605_,
        v_inst_3606_,
        v_inst_3607_,
        v_inst_3608_,
        v_inst_3609_,
        v_inst_3610_,
        v_stx_3611_,
    );
    return v___x_3612_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(
    mut v_a_3613_: *mut crate::leanh::LeanObject,
    mut v_toPure_3614_: *mut crate::leanh::LeanObject,
    mut v_s_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3616_, 0, v_a_3613_);
    crate::leanh::lean_ctor_set(v___x_3616_, 1, v_s_3615_);
    v___x_3617_ =
        crate::leanh::lean_apply_2(v_toPure_3614_, crate::leanh::lean_box(0), v___x_3616_);
    return v___x_3617_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(
    mut v_toPure_3618_: *mut crate::leanh::LeanObject,
    mut v_ref_3619_: *mut crate::leanh::LeanObject,
    mut v_inst_3620_: *mut crate::leanh::LeanObject,
    mut v_toBind_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3623_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3623_, 0, v_a_3622_);
    crate::leanh::lean_closure_set(v___f_3623_, 1, v_toPure_3618_);
    v___x_3624_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3624_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3624_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3624_, 2, v_ref_3619_);
    v___x_3625_ = crate::leanh::lean_apply_2(v_inst_3620_, crate::leanh::lean_box(0), v___x_3624_);
    v___x_3626_ = crate::leanh::lean_apply_4(
        v_toBind_3621_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3625_,
        v___f_3623_,
    );
    return v___x_3626_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(
    mut v_toPure_3627_: *mut crate::leanh::LeanObject,
    mut v_inst_3628_: *mut crate::leanh::LeanObject,
    mut v_toBind_3629_: *mut crate::leanh::LeanObject,
    mut v___x_3630_: *mut crate::leanh::LeanObject,
    mut v___x_3631_: *mut crate::leanh::LeanObject,
    mut v___x_3632_: *mut crate::leanh::LeanObject,
    mut v___x_3633_: *mut crate::leanh::LeanObject,
    mut v___x_3634_: *mut crate::leanh::LeanObject,
    mut v___f_3635_: *mut crate::leanh::LeanObject,
    mut v___x_3636_: *mut crate::leanh::LeanObject,
    mut v___x_3637_: *mut crate::leanh::LeanObject,
    mut v___x_3638_: *mut crate::leanh::LeanObject,
    mut v_nss_3639_: *mut crate::leanh::LeanObject,
    mut v_idStx_3640_: *mut crate::leanh::LeanObject,
    mut v_ref_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100__overap_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_3629_);
    crate::leanh::lean_inc(v_ref_3641_);
    v___f_3642_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3642_, 0, v_toPure_3627_);
    crate::leanh::lean_closure_set(v___f_3642_, 1, v_ref_3641_);
    crate::leanh::lean_closure_set(v___f_3642_, 2, v_inst_3628_);
    crate::leanh::lean_closure_set(v___f_3642_, 3, v_toBind_3629_);
    v___x_100__overap_3643_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
        v___x_3630_,
        v___x_3631_,
        v___x_3632_,
        v___x_3633_,
        v___x_3634_,
        v___f_3635_,
        v___x_3636_,
        v___x_3637_,
        v___x_3638_,
        v_nss_3639_,
        v_idStx_3640_,
    );
    v___x_3644_ = crate::leanh::lean_apply_1(v___x_100__overap_3643_, v_ref_3641_);
    v___x_3645_ = crate::leanh::lean_apply_4(
        v_toBind_3629_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3644_,
        v___f_3642_,
    );
    return v___x_3645_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(
    mut v_toPure_3646_: *mut crate::leanh::LeanObject,
    mut v_____x_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3648_ = crate::leanh::lean_ctor_get(v_____x_3647_, 0);
    crate::leanh::lean_inc(v_fst_3648_);
    crate::leanh::lean_dec_ref(v_____x_3647_);
    v___x_3649_ =
        crate::leanh::lean_apply_2(v_toPure_3646_, crate::leanh::lean_box(0), v_fst_3648_);
    return v___x_3649_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(
    mut v_toApplicative_3650_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3651_: *mut crate::leanh::LeanObject,
    mut v_inst_3652_: *mut crate::leanh::LeanObject,
    mut v_toBind_3653_: *mut crate::leanh::LeanObject,
    mut v___x_3654_: *mut crate::leanh::LeanObject,
    mut v___x_3655_: *mut crate::leanh::LeanObject,
    mut v___x_3656_: *mut crate::leanh::LeanObject,
    mut v___x_3657_: *mut crate::leanh::LeanObject,
    mut v___x_3658_: *mut crate::leanh::LeanObject,
    mut v___f_3659_: *mut crate::leanh::LeanObject,
    mut v___x_3660_: *mut crate::leanh::LeanObject,
    mut v___x_3661_: *mut crate::leanh::LeanObject,
    mut v___x_3662_: *mut crate::leanh::LeanObject,
    mut v_nss_3663_: *mut crate::leanh::LeanObject,
    mut v_idStx_3664_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3666_ = crate::leanh::lean_ctor_get(v_toApplicative_3650_, 1);
    crate::leanh::lean_inc_n(v_toPure_3666_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3650_);
    v___x_3667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3667_, 0, v_____do__lift_3651_);
    crate::leanh::lean_ctor_set(v___x_3667_, 1, v_____do__lift_3665_);
    v___x_3668_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3668_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3668_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3668_, 2, v___x_3667_);
    crate::leanh::lean_inc(v_inst_3652_);
    v___x_3669_ = crate::leanh::lean_apply_2(v_inst_3652_, crate::leanh::lean_box(0), v___x_3668_);
    crate::leanh::lean_inc_n(v_toBind_3653_, 2);
    v___f_3670_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2 as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_3670_, 0, v_toPure_3666_);
    crate::leanh::lean_closure_set(v___f_3670_, 1, v_inst_3652_);
    crate::leanh::lean_closure_set(v___f_3670_, 2, v_toBind_3653_);
    crate::leanh::lean_closure_set(v___f_3670_, 3, v___x_3654_);
    crate::leanh::lean_closure_set(v___f_3670_, 4, v___x_3655_);
    crate::leanh::lean_closure_set(v___f_3670_, 5, v___x_3656_);
    crate::leanh::lean_closure_set(v___f_3670_, 6, v___x_3657_);
    crate::leanh::lean_closure_set(v___f_3670_, 7, v___x_3658_);
    crate::leanh::lean_closure_set(v___f_3670_, 8, v___f_3659_);
    crate::leanh::lean_closure_set(v___f_3670_, 9, v___x_3660_);
    crate::leanh::lean_closure_set(v___f_3670_, 10, v___x_3661_);
    crate::leanh::lean_closure_set(v___f_3670_, 11, v___x_3662_);
    crate::leanh::lean_closure_set(v___f_3670_, 12, v_nss_3663_);
    crate::leanh::lean_closure_set(v___f_3670_, 13, v_idStx_3664_);
    v___f_3671_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3671_, 0, v_toPure_3666_);
    v___x_3672_ = crate::leanh::lean_apply_4(
        v_toBind_3653_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3669_,
        v___f_3670_,
    );
    v___x_3673_ = crate::leanh::lean_apply_4(
        v_toBind_3653_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3672_,
        v___f_3671_,
    );
    return v___x_3673_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(
    mut v_toApplicative_3674_: *mut crate::leanh::LeanObject,
    mut v_inst_3675_: *mut crate::leanh::LeanObject,
    mut v_toBind_3676_: *mut crate::leanh::LeanObject,
    mut v___x_3677_: *mut crate::leanh::LeanObject,
    mut v___x_3678_: *mut crate::leanh::LeanObject,
    mut v___x_3679_: *mut crate::leanh::LeanObject,
    mut v___x_3680_: *mut crate::leanh::LeanObject,
    mut v___x_3681_: *mut crate::leanh::LeanObject,
    mut v___f_3682_: *mut crate::leanh::LeanObject,
    mut v___x_3683_: *mut crate::leanh::LeanObject,
    mut v___x_3684_: *mut crate::leanh::LeanObject,
    mut v___x_3685_: *mut crate::leanh::LeanObject,
    mut v_nss_3686_: *mut crate::leanh::LeanObject,
    mut v_idStx_3687_: *mut crate::leanh::LeanObject,
    mut v_getCurrNamespace_3688_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_3676_);
    v___f_3690_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4 as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_3690_, 0, v_toApplicative_3674_);
    crate::leanh::lean_closure_set(v___f_3690_, 1, v_____do__lift_3689_);
    crate::leanh::lean_closure_set(v___f_3690_, 2, v_inst_3675_);
    crate::leanh::lean_closure_set(v___f_3690_, 3, v_toBind_3676_);
    crate::leanh::lean_closure_set(v___f_3690_, 4, v___x_3677_);
    crate::leanh::lean_closure_set(v___f_3690_, 5, v___x_3678_);
    crate::leanh::lean_closure_set(v___f_3690_, 6, v___x_3679_);
    crate::leanh::lean_closure_set(v___f_3690_, 7, v___x_3680_);
    crate::leanh::lean_closure_set(v___f_3690_, 8, v___x_3681_);
    crate::leanh::lean_closure_set(v___f_3690_, 9, v___f_3682_);
    crate::leanh::lean_closure_set(v___f_3690_, 10, v___x_3683_);
    crate::leanh::lean_closure_set(v___f_3690_, 11, v___x_3684_);
    crate::leanh::lean_closure_set(v___f_3690_, 12, v___x_3685_);
    crate::leanh::lean_closure_set(v___f_3690_, 13, v_nss_3686_);
    crate::leanh::lean_closure_set(v___f_3690_, 14, v_idStx_3687_);
    v___x_3691_ = crate::leanh::lean_apply_4(
        v_toBind_3676_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_3688_,
        v___f_3690_,
    );
    return v___x_3691_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(
    mut v_inst_3692_: *mut crate::leanh::LeanObject,
    mut v_inst_3693_: *mut crate::leanh::LeanObject,
    mut v_inst_3694_: *mut crate::leanh::LeanObject,
    mut v_inst_3695_: *mut crate::leanh::LeanObject,
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
    mut v_inst_3697_: *mut crate::leanh::LeanObject,
    mut v_inst_3698_: *mut crate::leanh::LeanObject,
    mut v_inst_3699_: *mut crate::leanh::LeanObject,
    mut v_inst_3700_: *mut crate::leanh::LeanObject,
    mut v_nss_3701_: *mut crate::leanh::LeanObject,
    mut v_idStx_3702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3703_ = crate::leanh::lean_ctor_get(v_inst_3692_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3703_);
                v_toBind_3704_ = crate::leanh::lean_ctor_get(v_inst_3692_, 1);
                crate::leanh::lean_inc(v_toBind_3704_);
                v_getCurrNamespace_3705_ = crate::leanh::lean_ctor_get(v_inst_3700_, 0);
                v_getOpenDecls_3706_ = crate::leanh::lean_ctor_get(v_inst_3700_, 1);
                v_isSharedCheck_3737_ = (!crate::leanh::lean_is_exclusive(v_inst_3700_)) as u8;
                if v_isSharedCheck_3737_ == 0 {
                    v___x_3708_ = v_inst_3700_;
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_getOpenDecls_3706_);
                    crate::leanh::lean_inc(v_getCurrNamespace_3705_);
                    crate::leanh::lean_dec(v_inst_3700_);
                    v___x_3708_ = crate::leanh::lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_3692_);
                v___x_3710_ = l_StateRefT_x27_instMonad___redArg(v_inst_3692_);
                v_getEnv_3711_ = crate::leanh::lean_ctor_get(v_inst_3693_, 0);
                v_modifyEnv_3712_ = crate::leanh::lean_ctor_get(v_inst_3693_, 1);
                v_isSharedCheck_3736_ = (!crate::leanh::lean_is_exclusive(v_inst_3693_)) as u8;
                if v_isSharedCheck_3736_ == 0 {
                    v___x_3714_ = v_inst_3693_;
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyEnv_3712_);
                    crate::leanh::lean_inc(v_getEnv_3711_);
                    crate::leanh::lean_dec(v_inst_3693_);
                    v___x_3714_ = crate::leanh::lean_box(0);
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3716_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3717_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3717_, 0, v_modifyEnv_3712_);
                crate::leanh::lean_closure_set(v___f_3717_, 1, v___x_3716_);
                v___x_3718_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3718_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3718_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3718_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3718_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3718_, 4, v_getEnv_3711_);
                if v_isShared_3715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3714_, 1, v___f_3717_);
                    crate::leanh::lean_ctor_set(v___x_3714_, 0, v___x_3718_);
                    v___x_3720_ = v___x_3714_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___f_3717_);
                    v___x_3720_ = v_reuseFailAlloc_3735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_inst_3694_);
                v___f_3721_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3721_, 0, v_inst_3694_);
                v___f_3722_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3722_, 0, v_inst_3694_);
                if v_isShared_3709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3708_, 1, v___f_3722_);
                    crate::leanh::lean_ctor_set(v___x_3708_, 0, v___f_3721_);
                    v___x_3724_ = v___x_3708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___f_3721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___f_3722_);
                    v___x_3724_ = v_reuseFailAlloc_3734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3725_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3726_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3716_,
                    v___x_3725_,
                    v_inst_3695_,
                );
                v___f_3727_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3727_, 0, v_inst_3696_);
                crate::leanh::lean_closure_set(v___f_3727_, 1, v___x_3716_);
                crate::leanh::lean_inc_ref(v___x_3710_);
                crate::leanh::lean_inc_ref(v___f_3727_);
                v___x_3728_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3727_,
                    v___x_3710_,
                );
                v___x_3729_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3716_, v_inst_3698_);
                v___x_3730_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3730_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3730_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3730_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3730_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3730_, 4, v_inst_3699_);
                crate::leanh::lean_inc(v_inst_3697_);
                v___x_3731_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3692_, v_inst_3697_);
                crate::leanh::lean_inc(v_toBind_3704_);
                v___f_3732_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_3732_, 0, v_toApplicative_3703_);
                crate::leanh::lean_closure_set(v___f_3732_, 1, v_inst_3697_);
                crate::leanh::lean_closure_set(v___f_3732_, 2, v_toBind_3704_);
                crate::leanh::lean_closure_set(v___f_3732_, 3, v___x_3710_);
                crate::leanh::lean_closure_set(v___f_3732_, 4, v___x_3720_);
                crate::leanh::lean_closure_set(v___f_3732_, 5, v___x_3724_);
                crate::leanh::lean_closure_set(v___f_3732_, 6, v___x_3726_);
                crate::leanh::lean_closure_set(v___f_3732_, 7, v___x_3728_);
                crate::leanh::lean_closure_set(v___f_3732_, 8, v___f_3727_);
                crate::leanh::lean_closure_set(v___f_3732_, 9, v___x_3729_);
                crate::leanh::lean_closure_set(v___f_3732_, 10, v___x_3730_);
                crate::leanh::lean_closure_set(v___f_3732_, 11, v___x_3731_);
                crate::leanh::lean_closure_set(v___f_3732_, 12, v_nss_3701_);
                crate::leanh::lean_closure_set(v___f_3732_, 13, v_idStx_3702_);
                crate::leanh::lean_closure_set(v___f_3732_, 14, v_getCurrNamespace_3705_);
                v___x_3733_ = crate::leanh::lean_apply_4(
                    v_toBind_3704_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getOpenDecls_3706_,
                    v___f_3732_,
                );
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(
    mut v_m_3738_: *mut crate::leanh::LeanObject,
    mut v_inst_3739_: *mut crate::leanh::LeanObject,
    mut v_inst_3740_: *mut crate::leanh::LeanObject,
    mut v_inst_3741_: *mut crate::leanh::LeanObject,
    mut v_inst_3742_: *mut crate::leanh::LeanObject,
    mut v_inst_3743_: *mut crate::leanh::LeanObject,
    mut v_inst_3744_: *mut crate::leanh::LeanObject,
    mut v_inst_3745_: *mut crate::leanh::LeanObject,
    mut v_inst_3746_: *mut crate::leanh::LeanObject,
    mut v_inst_3747_: *mut crate::leanh::LeanObject,
    mut v_nss_3748_: *mut crate::leanh::LeanObject,
    mut v_idStx_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(
        v_inst_3739_,
        v_inst_3740_,
        v_inst_3741_,
        v_inst_3742_,
        v_inst_3743_,
        v_inst_3744_,
        v_inst_3745_,
        v_inst_3746_,
        v_inst_3747_,
        v_nss_3748_,
        v_idStx_3749_,
    );
    return v___x_3750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Open(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Open(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Open(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Open(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Open(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Open(builtin);
}
