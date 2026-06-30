// Lean compiler output
// Module: Lean.Elab.Open
// Imports: Lean.Elab.Util Lean.Parser.Command Lean.Parser.Command Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat,
};
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
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_MessageData_ofExpr as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 111, 112, 101, 110, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value:
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
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value:
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
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value:
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
    m_data: [111, 112, 101, 110, 79, 110, 108, 121, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value:
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
    m_data: [111, 112, 101, 110, 82, 101, 110, 97, 109, 105, 110, 103, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value:
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
    m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value:
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
    m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value:
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
    m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value:
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
    m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value:
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
    m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value:
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
    m_fun: l_Option_map as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value:
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
    m_fun: l_Option_bind as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value:
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut leanh::LeanObject)],
};
pub static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
            as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
            as *mut leanh::LeanObject,
        4840083868155834027 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value:
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
    m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value:
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
    m_fun: l_Lean_TSyntax_getId___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
    mut v_inst_1876_: *mut leanh::LeanObject,
    mut v_____do__lift_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = leanh::lean_ctor_get(v_inst_1876_, 0);
    leanh::lean_inc_ref(v_toApplicative_1879_);
    leanh::lean_dec_ref(v_inst_1876_);
    v_currNamespace_1880_ = leanh::lean_ctor_get(v_____do__lift_1877_, 1);
    leanh::lean_inc(v_currNamespace_1880_);
    leanh::lean_dec_ref(v_____do__lift_1877_);
    v_toPure_1881_ = leanh::lean_ctor_get(v_toApplicative_1879_, 1);
    leanh::lean_inc(v_toPure_1881_);
    leanh::lean_dec_ref(v_toApplicative_1879_);
    v___x_1882_ = leanh::lean_apply_2(
        v_toPure_1881_,
        leanh::lean_box(0),
        v_currNamespace_1880_,
    );
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(
    mut v_inst_1883_: *mut leanh::LeanObject,
    mut v_____do__lift_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
        v_inst_1883_,
        v_____do__lift_1884_,
        v___y_1885_,
    );
    leanh::lean_dec(v___y_1885_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
    mut v_inst_1887_: *mut leanh::LeanObject,
    mut v_____do__lift_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1890_ = leanh::lean_ctor_get(v_inst_1887_, 0);
    leanh::lean_inc_ref(v_toApplicative_1890_);
    leanh::lean_dec_ref(v_inst_1887_);
    v_openDecls_1891_ = leanh::lean_ctor_get(v_____do__lift_1888_, 0);
    leanh::lean_inc(v_openDecls_1891_);
    leanh::lean_dec_ref(v_____do__lift_1888_);
    v_toPure_1892_ = leanh::lean_ctor_get(v_toApplicative_1890_, 1);
    leanh::lean_inc(v_toPure_1892_);
    leanh::lean_dec_ref(v_toApplicative_1890_);
    v___x_1893_ =
        leanh::lean_apply_2(v_toPure_1892_, leanh::lean_box(0), v_openDecls_1891_);
    return v___x_1893_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(
    mut v_inst_1894_: *mut leanh::LeanObject,
    mut v_____do__lift_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
        v_inst_1894_,
        v_____do__lift_1895_,
        v___y_1896_,
    );
    leanh::lean_dec(v___y_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
    mut v_inst_1898_: *mut leanh::LeanObject,
    mut v_inst_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1898_, 3);
    v___f_1900_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1900_, 0, v_inst_1898_);
    v___f_1901_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1901_, 0, v_inst_1898_);
    v___x_1902_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1902_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1902_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1902_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1902_, 3, v_inst_1899_);
    leanh::lean_inc_ref(v___x_1902_);
    v___x_1903_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_1903_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1903_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1903_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1903_, 3, v_inst_1898_);
    leanh::lean_closure_set(v___x_1903_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1903_, 5, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1903_, 6, v___x_1902_);
    leanh::lean_closure_set(v___x_1903_, 7, v___f_1900_);
    v___x_1904_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_1904_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1904_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1904_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1904_, 3, v_inst_1898_);
    leanh::lean_closure_set(v___x_1904_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1904_, 5, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1904_, 6, v___x_1902_);
    leanh::lean_closure_set(v___x_1904_, 7, v___f_1901_);
    v___x_1905_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1905_, 0, v___x_1903_);
    leanh::lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM(
    mut v_m_1906_: *mut leanh::LeanObject,
    mut v_inst_1907_: *mut leanh::LeanObject,
    mut v_inst_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1907_, v_inst_1908_);
    return v___x_1909_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
    mut v_idStx_1910_: *mut leanh::LeanObject,
    mut v_withRef_1911_: *mut leanh::LeanObject,
    mut v___x_1912_: *mut leanh::LeanObject,
    mut v_oldRef_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1914_ = l_Lean_replaceRef(v_idStx_1910_, v_oldRef_1913_);
    v___x_1915_ = leanh::lean_apply_3(
        v_withRef_1911_,
        leanh::lean_box(0),
        v_ref_1914_,
        v___x_1912_,
    );
    return v___x_1915_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(
    mut v_idStx_1916_: *mut leanh::LeanObject,
    mut v_withRef_1917_: *mut leanh::LeanObject,
    mut v___x_1918_: *mut leanh::LeanObject,
    mut v_oldRef_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
        v_idStx_1916_,
        v_withRef_1917_,
        v___x_1918_,
        v_oldRef_1919_,
    );
    leanh::lean_dec(v_oldRef_1919_);
    leanh::lean_dec(v_idStx_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(
    mut v_declName_1921_: *mut leanh::LeanObject,
    mut v_inst_1922_: *mut leanh::LeanObject,
    mut v_inst_1923_: *mut leanh::LeanObject,
    mut v_inst_1924_: *mut leanh::LeanObject,
    mut v_inst_1925_: *mut leanh::LeanObject,
    mut v_inst_1926_: *mut leanh::LeanObject,
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_inst_1928_: *mut leanh::LeanObject,
    mut v_inst_1929_: *mut leanh::LeanObject,
    mut v_inst_1930_: *mut leanh::LeanObject,
    mut v_idStx_1931_: *mut leanh::LeanObject,
    mut v_toBind_1932_: *mut leanh::LeanObject,
    mut v_toApplicative_1933_: *mut leanh::LeanObject,
    mut v_____do__lift_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    v___x_1935_ = 1;
    leanh::lean_inc(v_declName_1921_);
    v___x_1936_ = l_Lean_Environment_contains(v_____do__lift_1934_, v_declName_1921_, v___x_1935_);
    if v___x_1936_ == 0 {
        let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getRef_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_withRef_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_1933_);
        leanh::lean_inc_ref(v_inst_1923_);
        v___x_1937_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1937_, 0, v_inst_1922_);
        leanh::lean_ctor_set(v___x_1937_, 1, v_inst_1923_);
        leanh::lean_ctor_set(v___x_1937_, 2, v_inst_1924_);
        v_getRef_1938_ = leanh::lean_ctor_get(v_inst_1923_, 0);
        leanh::lean_inc(v_getRef_1938_);
        v_withRef_1939_ = leanh::lean_ctor_get(v_inst_1923_, 1);
        leanh::lean_inc(v_withRef_1939_);
        leanh::lean_dec_ref(v_inst_1923_);
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
        v___f_1941_ = leanh::lean_alloc_closure(
            l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1941_, 0, v_idStx_1931_);
        leanh::lean_closure_set(v___f_1941_, 1, v_withRef_1939_);
        leanh::lean_closure_set(v___f_1941_, 2, v___x_1940_);
        v___x_1942_ = leanh::lean_apply_4(
            v_toBind_1932_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getRef_1938_,
            v___f_1941_,
        );
        return v___x_1942_;
    } else {
        let mut v_toPure_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_1932_);
        leanh::lean_dec(v_idStx_1931_);
        leanh::lean_dec(v_inst_1930_);
        leanh::lean_dec_ref(v_inst_1929_);
        leanh::lean_dec(v_inst_1928_);
        leanh::lean_dec_ref(v_inst_1927_);
        leanh::lean_dec_ref(v_inst_1926_);
        leanh::lean_dec_ref(v_inst_1925_);
        leanh::lean_dec(v_inst_1924_);
        leanh::lean_dec_ref(v_inst_1923_);
        leanh::lean_dec_ref(v_inst_1922_);
        v_toPure_1943_ = leanh::lean_ctor_get(v_toApplicative_1933_, 1);
        leanh::lean_inc(v_toPure_1943_);
        leanh::lean_dec_ref(v_toApplicative_1933_);
        v___x_1944_ =
            leanh::lean_apply_2(v_toPure_1943_, leanh::lean_box(0), v_declName_1921_);
        return v___x_1944_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg(
    mut v_inst_1945_: *mut leanh::LeanObject,
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_inst_1947_: *mut leanh::LeanObject,
    mut v_inst_1948_: *mut leanh::LeanObject,
    mut v_inst_1949_: *mut leanh::LeanObject,
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_inst_1951_: *mut leanh::LeanObject,
    mut v_inst_1952_: *mut leanh::LeanObject,
    mut v_inst_1953_: *mut leanh::LeanObject,
    mut v_ns_1954_: *mut leanh::LeanObject,
    mut v_idStx_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1956_ = leanh::lean_ctor_get(v_inst_1945_, 0);
    leanh::lean_inc_ref(v_toApplicative_1956_);
    v_toBind_1957_ = leanh::lean_ctor_get(v_inst_1945_, 1);
    leanh::lean_inc_n(v_toBind_1957_, 2);
    v_getEnv_1958_ = leanh::lean_ctor_get(v_inst_1946_, 0);
    leanh::lean_inc(v_getEnv_1958_);
    v___x_1959_ = l_Lean_Syntax_getId(v_idStx_1955_);
    v_declName_1960_ = l_Lean_Name_append(v_ns_1954_, v___x_1959_);
    v___f_1961_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_1961_, 0, v_declName_1960_);
    leanh::lean_closure_set(v___f_1961_, 1, v_inst_1947_);
    leanh::lean_closure_set(v___f_1961_, 2, v_inst_1948_);
    leanh::lean_closure_set(v___f_1961_, 3, v_inst_1949_);
    leanh::lean_closure_set(v___f_1961_, 4, v_inst_1945_);
    leanh::lean_closure_set(v___f_1961_, 5, v_inst_1953_);
    leanh::lean_closure_set(v___f_1961_, 6, v_inst_1946_);
    leanh::lean_closure_set(v___f_1961_, 7, v_inst_1952_);
    leanh::lean_closure_set(v___f_1961_, 8, v_inst_1951_);
    leanh::lean_closure_set(v___f_1961_, 9, v_inst_1950_);
    leanh::lean_closure_set(v___f_1961_, 10, v_idStx_1955_);
    leanh::lean_closure_set(v___f_1961_, 11, v_toBind_1957_);
    leanh::lean_closure_set(v___f_1961_, 12, v_toApplicative_1956_);
    v___x_1962_ = leanh::lean_apply_4(
        v_toBind_1957_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1958_,
        v___f_1961_,
    );
    return v___x_1962_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId(
    mut v_m_1963_: *mut leanh::LeanObject,
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_inst_1966_: *mut leanh::LeanObject,
    mut v_inst_1967_: *mut leanh::LeanObject,
    mut v_inst_1968_: *mut leanh::LeanObject,
    mut v_inst_1969_: *mut leanh::LeanObject,
    mut v_inst_1970_: *mut leanh::LeanObject,
    mut v_inst_1971_: *mut leanh::LeanObject,
    mut v_inst_1972_: *mut leanh::LeanObject,
    mut v_ns_1973_: *mut leanh::LeanObject,
    mut v_idStx_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_decl_1976_: *mut leanh::LeanObject,
    mut v_s_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_openDecls_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_openDecls_1978_ = leanh::lean_ctor_get(v_s_1977_, 0);
                v_currNamespace_1979_ = leanh::lean_ctor_get(v_s_1977_, 1);
                v_isSharedCheck_1989_ = (!leanh::lean_is_exclusive(v_s_1977_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v___x_1981_ = v_s_1977_;
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_currNamespace_1979_);
                    leanh::lean_inc(v_openDecls_1978_);
                    leanh::lean_dec(v_s_1977_);
                    v___x_1981_ = leanh::lean_box(0);
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1983_ = leanh::lean_box(0);
                v___x_1984_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1984_, 0, v_decl_1976_);
                leanh::lean_ctor_set(v___x_1984_, 1, v_openDecls_1978_);
                if v_isShared_1982_ == 0 {
                    leanh::lean_ctor_set(v___x_1981_, 0, v___x_1984_);
                    v___x_1986_ = v___x_1981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_currNamespace_1979_);
                    v___x_1986_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1987_, 0, v___x_1983_);
                leanh::lean_ctor_set(v___x_1987_, 1, v___x_1986_);
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
    mut v_inst_1990_: *mut leanh::LeanObject,
    mut v_decl_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1993_ = leanh::lean_alloc_closure(
        l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1993_, 0, v_decl_1991_);
    leanh::lean_inc(v_a_1992_);
    v___x_1994_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_1994_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1994_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1994_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1994_, 3, v_a_1992_);
    leanh::lean_closure_set(v___x_1994_, 4, v___f_1993_);
    v___x_1995_ = leanh::lean_apply_2(v_inst_1990_, leanh::lean_box(0), v___x_1994_);
    return v___x_1995_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(
    mut v_inst_1996_: *mut leanh::LeanObject,
    mut v_decl_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1999_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_1996_,
        v_decl_1997_,
        v_a_1998_,
    );
    leanh::lean_dec(v_a_1998_);
    return v_res_1999_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
    mut v_m_2000_: *mut leanh::LeanObject,
    mut v_inst_2001_: *mut leanh::LeanObject,
    mut v_decl_2002_: *mut leanh::LeanObject,
    mut v_a_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2001_,
        v_decl_2002_,
        v_a_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(
    mut v_m_2005_: *mut leanh::LeanObject,
    mut v_inst_2006_: *mut leanh::LeanObject,
    mut v_decl_2007_: *mut leanh::LeanObject,
    mut v_a_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
        v_m_2005_,
        v_inst_2006_,
        v_decl_2007_,
        v_a_2008_,
    );
    leanh::lean_dec(v_a_2008_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(
    mut v_x_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = leanh::lean_box(0);
    v___x_2012_ = l_Lean_mkConst(v_x_2010_, v___x_2011_);
    return v___x_2012_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(
    mut v_toPure_2013_: *mut leanh::LeanObject,
    mut v_p_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2015_ = leanh::lean_ctor_get(v_p_2014_, 1);
                leanh::lean_inc(v_snd_2015_);
                leanh::lean_dec_ref(v_p_2014_);
                v_fst_2016_ = leanh::lean_ctor_get(v_snd_2015_, 0);
                v_snd_2017_ = leanh::lean_ctor_get(v_snd_2015_, 1);
                v_isSharedCheck_2026_ = (!leanh::lean_is_exclusive(v_snd_2015_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_2019_ = v_snd_2015_;
                    v_isShared_2020_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2017_);
                    leanh::lean_inc(v_fst_2016_);
                    leanh::lean_dec(v_snd_2015_);
                    v___x_2019_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fst_2016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_snd_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
                v___x_2024_ = leanh::lean_apply_2(
                    v_toPure_2013_,
                    leanh::lean_box(0),
                    v___x_2023_,
                );
                return v___x_2024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(
    mut v_snd_2027_: *mut leanh::LeanObject,
    mut v_fst_2028_: *mut leanh::LeanObject,
    mut v_toPure_2029_: *mut leanh::LeanObject,
    mut v_declName_2030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = lean_array_push(v_snd_2027_, v_declName_2030_);
    v___x_2032_ = leanh::lean_box(0);
    v___x_2033_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2033_, 0, v_fst_2028_);
    leanh::lean_ctor_set(v___x_2033_, 1, v___x_2031_);
    v___x_2034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2034_, 0, v___x_2032_);
    leanh::lean_ctor_set(v___x_2034_, 1, v___x_2033_);
    v___x_2035_ =
        leanh::lean_apply_2(v_toPure_2029_, leanh::lean_box(0), v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(
    mut v_fst_2036_: *mut leanh::LeanObject,
    mut v_snd_2037_: *mut leanh::LeanObject,
    mut v_toPure_2038_: *mut leanh::LeanObject,
    mut v_ex_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = lean_array_push(v_fst_2036_, v_ex_2039_);
    v___x_2041_ = leanh::lean_box(0);
    v___x_2042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2042_, 0, v___x_2040_);
    leanh::lean_ctor_set(v___x_2042_, 1, v_snd_2037_);
    v___x_2043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2041_);
    leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ =
        leanh::lean_apply_2(v_toPure_2038_, leanh::lean_box(0), v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(
    mut v_inst_2045_: *mut leanh::LeanObject,
    mut v_toPure_2046_: *mut leanh::LeanObject,
    mut v_inst_2047_: *mut leanh::LeanObject,
    mut v_inst_2048_: *mut leanh::LeanObject,
    mut v_inst_2049_: *mut leanh::LeanObject,
    mut v_inst_2050_: *mut leanh::LeanObject,
    mut v_inst_2051_: *mut leanh::LeanObject,
    mut v_inst_2052_: *mut leanh::LeanObject,
    mut v_inst_2053_: *mut leanh::LeanObject,
    mut v_inst_2054_: *mut leanh::LeanObject,
    mut v_idStx_2055_: *mut leanh::LeanObject,
    mut v_toBind_2056_: *mut leanh::LeanObject,
    mut v___f_2057_: *mut leanh::LeanObject,
    mut v_a_2058_: *mut leanh::LeanObject,
    mut v_x_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2061_ = leanh::lean_ctor_get(v___y_2060_, 0);
    leanh::lean_inc_n(v_fst_2061_, 2);
    v_snd_2062_ = leanh::lean_ctor_get(v___y_2060_, 1);
    leanh::lean_inc_n(v_snd_2062_, 2);
    leanh::lean_dec_ref(v___y_2060_);
    v_tryCatch_2063_ = leanh::lean_ctor_get(v_inst_2045_, 1);
    leanh::lean_inc(v_tryCatch_2063_);
    leanh::lean_inc(v_toPure_2046_);
    v___f_2064_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2064_, 0, v_snd_2062_);
    leanh::lean_closure_set(v___f_2064_, 1, v_fst_2061_);
    leanh::lean_closure_set(v___f_2064_, 2, v_toPure_2046_);
    v___f_2065_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2065_, 0, v_fst_2061_);
    leanh::lean_closure_set(v___f_2065_, 1, v_snd_2062_);
    leanh::lean_closure_set(v___f_2065_, 2, v_toPure_2046_);
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
    leanh::lean_inc(v_toBind_2056_);
    v___x_2067_ = leanh::lean_apply_4(
        v_toBind_2056_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2066_,
        v___f_2064_,
    );
    v___x_2068_ = leanh::lean_apply_3(
        v_tryCatch_2063_,
        leanh::lean_box(0),
        v___x_2067_,
        v___f_2065_,
    );
    v___x_2069_ = leanh::lean_apply_4(
        v_toBind_2056_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2068_,
        v___f_2057_,
    );
    return v___x_2069_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10;
    v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12;
    v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(
    mut v_snd_2096_: *mut leanh::LeanObject,
    mut v_inst_2097_: *mut leanh::LeanObject,
    mut v_inst_2098_: *mut leanh::LeanObject,
    mut v_inst_2099_: *mut leanh::LeanObject,
    mut v_idStx_2100_: *mut leanh::LeanObject,
    mut v___f_2101_: *mut leanh::LeanObject,
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_toBind_2103_: *mut leanh::LeanObject,
    mut v___x_2104_: *mut leanh::LeanObject,
    mut v_toPure_2105_: *mut leanh::LeanObject,
    mut v_____r_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_sz_2117_: usize = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2107_ = lean_array_get_size(v_snd_2096_);
                v___x_2108_ = leanh::lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_dec_eq(v___x_2107_, v___x_2108_);
                if v___x_2109_ == 0 {
                    leanh::lean_dec(v_toPure_2105_);
                    leanh::lean_inc_ref(v_inst_2098_);
                    v___x_2110_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2110_, 0, v_inst_2097_);
                    leanh::lean_ctor_set(v___x_2110_, 1, v_inst_2098_);
                    leanh::lean_ctor_set(v___x_2110_, 2, v_inst_2099_);
                    v___x_2111_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_getRef_2112_ = leanh::lean_ctor_get(v_inst_2098_, 0);
                    v_withRef_2113_ = leanh::lean_ctor_get(v_inst_2098_, 1);
                    v_isSharedCheck_2137_ = (!leanh::lean_is_exclusive(v_inst_2098_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2115_ = v_inst_2098_;
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_withRef_2113_);
                        leanh::lean_inc(v_getRef_2112_);
                        leanh::lean_dec(v_inst_2098_);
                        v___x_2115_ = leanh::lean_box(0);
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toBind_2103_);
                    leanh::lean_dec_ref(v_inst_2102_);
                    leanh::lean_dec_ref(v___f_2101_);
                    leanh::lean_dec(v_idStx_2100_);
                    leanh::lean_dec(v_inst_2099_);
                    leanh::lean_dec_ref(v_inst_2098_);
                    leanh::lean_dec_ref(v_inst_2097_);
                    v___x_2138_ = lean_array_fget(v_snd_2096_, v___x_2104_);
                    leanh::lean_dec(v_snd_2096_);
                    v___x_2139_ = leanh::lean_apply_2(
                        v_toPure_2105_,
                        leanh::lean_box(0),
                        v___x_2138_,
                    );
                    return v___x_2139_;
                }
            }
            1 => {
                v_sz_2117_ = lean_array_size(v_snd_2096_);
                v___x_2118_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
                v___x_2119_ = l_Lean_Syntax_getId(v_idStx_2100_);
                v___x_2120_ = l_Lean_MessageData_ofName(v___x_2119_);
                if v_isShared_2116_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2115_, 7);
                    leanh::lean_ctor_set(v___x_2115_, 1, v___x_2120_);
                    leanh::lean_ctor_set(v___x_2115_, 0, v___x_2118_);
                    v___x_2122_ = v___x_2115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2123_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
                v___x_2124_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2124_, 0, v___x_2122_);
                leanh::lean_ctor_set(v___x_2124_, 1, v___x_2123_);
                v___x_2125_ = 0usize;
                v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2111_,
                    v___f_2101_,
                    v_sz_2117_,
                    v___x_2125_,
                    v_snd_2096_,
                );
                v___x_2127_ = lean_array_to_list(v___x_2126_);
                v___x_2128_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14;
                v___x_2129_ = leanh::lean_box(0);
                v___x_2130_ = l_List_mapTR_loop___redArg(v___x_2128_, v___x_2127_, v___x_2129_);
                v___x_2131_ = l_Lean_MessageData_ofList(v___x_2130_);
                v___x_2132_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2132_, 0, v___x_2124_);
                leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                v___x_2133_ = l_Lean_throwError___redArg(v_inst_2102_, v___x_2110_, v___x_2132_);
                v___f_2134_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2134_, 0, v_idStx_2100_);
                leanh::lean_closure_set(v___f_2134_, 1, v_withRef_2113_);
                leanh::lean_closure_set(v___f_2134_, 2, v___x_2133_);
                v___x_2135_ = leanh::lean_apply_4(
                    v_toBind_2103_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_snd_2140_: *mut leanh::LeanObject,
    mut v_inst_2141_: *mut leanh::LeanObject,
    mut v_inst_2142_: *mut leanh::LeanObject,
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_idStx_2144_: *mut leanh::LeanObject,
    mut v___f_2145_: *mut leanh::LeanObject,
    mut v_inst_2146_: *mut leanh::LeanObject,
    mut v_toBind_2147_: *mut leanh::LeanObject,
    mut v___x_2148_: *mut leanh::LeanObject,
    mut v_toPure_2149_: *mut leanh::LeanObject,
    mut v_____r_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___x_2148_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(
    mut v___f_2152_: *mut leanh::LeanObject,
    mut v_____r_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2154_ = leanh::lean_apply_1(v___f_2152_, v_____r_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
    mut v_idStx_2155_: *mut leanh::LeanObject,
    mut v_withRef_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
    mut v_oldRef_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2159_ = l_Lean_replaceRef(v_idStx_2155_, v_oldRef_2158_);
    v___x_2160_ = leanh::lean_apply_3(
        v_withRef_2156_,
        leanh::lean_box(0),
        v_ref_2159_,
        v___y_2157_,
    );
    return v___x_2160_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(
    mut v_idStx_2161_: *mut leanh::LeanObject,
    mut v_withRef_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v_oldRef_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
        v_idStx_2161_,
        v_withRef_2162_,
        v___y_2163_,
        v_oldRef_2164_,
    );
    leanh::lean_dec(v_oldRef_2164_);
    leanh::lean_dec(v_idStx_2161_);
    return v_res_2165_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1;
    v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(
    mut v_inst_2171_: *mut leanh::LeanObject,
    mut v_inst_2172_: *mut leanh::LeanObject,
    mut v_inst_2173_: *mut leanh::LeanObject,
    mut v_idStx_2174_: *mut leanh::LeanObject,
    mut v___f_2175_: *mut leanh::LeanObject,
    mut v_inst_2176_: *mut leanh::LeanObject,
    mut v_toBind_2177_: *mut leanh::LeanObject,
    mut v___x_2178_: *mut leanh::LeanObject,
    mut v_toPure_2179_: *mut leanh::LeanObject,
    mut v_nss_2180_: *mut leanh::LeanObject,
    mut v_inst_2181_: *mut leanh::LeanObject,
    mut v_____s_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2183_ = leanh::lean_ctor_get(v_____s_2182_, 0);
                leanh::lean_inc(v_fst_2183_);
                v_snd_2184_ = leanh::lean_ctor_get(v_____s_2182_, 1);
                leanh::lean_inc_n(v_snd_2184_, 2);
                leanh::lean_dec_ref(v_____s_2182_);
                leanh::lean_inc(v_toPure_2179_);
                leanh::lean_inc(v___x_2178_);
                leanh::lean_inc(v_toBind_2177_);
                leanh::lean_inc_ref(v_inst_2176_);
                leanh::lean_inc_ref(v___f_2175_);
                leanh::lean_inc(v_idStx_2174_);
                leanh::lean_inc(v_inst_2173_);
                leanh::lean_inc_ref(v_inst_2172_);
                leanh::lean_inc_ref(v_inst_2171_);
                v___f_2185_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    11,
                    10,
                );
                leanh::lean_closure_set(v___f_2185_, 0, v_snd_2184_);
                leanh::lean_closure_set(v___f_2185_, 1, v_inst_2171_);
                leanh::lean_closure_set(v___f_2185_, 2, v_inst_2172_);
                leanh::lean_closure_set(v___f_2185_, 3, v_inst_2173_);
                leanh::lean_closure_set(v___f_2185_, 4, v_idStx_2174_);
                leanh::lean_closure_set(v___f_2185_, 5, v___f_2175_);
                leanh::lean_closure_set(v___f_2185_, 6, v_inst_2176_);
                leanh::lean_closure_set(v___f_2185_, 7, v_toBind_2177_);
                leanh::lean_closure_set(v___f_2185_, 8, v___x_2178_);
                leanh::lean_closure_set(v___f_2185_, 9, v_toPure_2179_);
                v___x_2186_ = lean_array_get_size(v_fst_2183_);
                v___x_2187_ = l_List_lengthTR___redArg(v_nss_2180_);
                v___x_2188_ = lean_nat_dec_eq(v___x_2186_, v___x_2187_);
                leanh::lean_dec(v___x_2187_);
                if v___x_2188_ == 0 {
                    leanh::lean_dec_ref(v___f_2185_);
                    leanh::lean_dec(v_fst_2183_);
                    leanh::lean_dec_ref(v_inst_2181_);
                    v___x_2189_ = leanh::lean_box(0);
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
                    leanh::lean_dec(v___x_2178_);
                    return v___x_2190_;
                } else {
                    leanh::lean_dec(v_snd_2184_);
                    leanh::lean_dec(v_toPure_2179_);
                    leanh::lean_dec_ref(v___f_2175_);
                    v___f_2191_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2191_, 0, v___f_2185_);
                    v___x_2199_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2200_ = lean_nat_dec_eq(v___x_2186_, v___x_2199_);
                    if v___x_2200_ == 0 {
                        leanh::lean_dec(v___x_2178_);
                        leanh::lean_inc_ref(v_inst_2172_);
                        v___x_2201_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2201_, 0, v_inst_2171_);
                        leanh::lean_ctor_set(v___x_2201_, 1, v_inst_2172_);
                        leanh::lean_ctor_set(v___x_2201_, 2, v_inst_2173_);
                        v___x_2202_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
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
                        leanh::lean_dec_ref(v_inst_2181_);
                        leanh::lean_dec_ref(v_inst_2176_);
                        leanh::lean_dec(v_inst_2173_);
                        v_throw_2204_ = leanh::lean_ctor_get(v_inst_2171_, 0);
                        leanh::lean_inc(v_throw_2204_);
                        leanh::lean_dec_ref(v_inst_2171_);
                        v___x_2205_ = lean_array_fget(v_fst_2183_, v___x_2178_);
                        leanh::lean_dec(v___x_2178_);
                        leanh::lean_dec(v_fst_2183_);
                        v___x_2206_ = leanh::lean_apply_2(
                            v_throw_2204_,
                            leanh::lean_box(0),
                            v___x_2205_,
                        );
                        v___y_2193_ = v___x_2206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_getRef_2194_ = leanh::lean_ctor_get(v_inst_2172_, 0);
                leanh::lean_inc(v_getRef_2194_);
                v_withRef_2195_ = leanh::lean_ctor_get(v_inst_2172_, 1);
                leanh::lean_inc(v_withRef_2195_);
                leanh::lean_dec_ref(v_inst_2172_);
                v___f_2196_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2196_, 0, v_idStx_2174_);
                leanh::lean_closure_set(v___f_2196_, 1, v_withRef_2195_);
                leanh::lean_closure_set(v___f_2196_, 2, v___y_2193_);
                leanh::lean_inc(v_toBind_2177_);
                v___x_2197_ = leanh::lean_apply_4(
                    v_toBind_2177_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getRef_2194_,
                    v___f_2196_,
                );
                v___x_2198_ = leanh::lean_apply_4(
                    v_toBind_2177_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_inst_2209_: *mut leanh::LeanObject,
    mut v_idStx_2210_: *mut leanh::LeanObject,
    mut v___f_2211_: *mut leanh::LeanObject,
    mut v_inst_2212_: *mut leanh::LeanObject,
    mut v_toBind_2213_: *mut leanh::LeanObject,
    mut v___x_2214_: *mut leanh::LeanObject,
    mut v_toPure_2215_: *mut leanh::LeanObject,
    mut v_nss_2216_: *mut leanh::LeanObject,
    mut v_inst_2217_: *mut leanh::LeanObject,
    mut v_____s_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_nss_2216_);
    return v_res_2219_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
    mut v_inst_2225_: *mut leanh::LeanObject,
    mut v_inst_2226_: *mut leanh::LeanObject,
    mut v_inst_2227_: *mut leanh::LeanObject,
    mut v_inst_2228_: *mut leanh::LeanObject,
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_inst_2231_: *mut leanh::LeanObject,
    mut v_inst_2232_: *mut leanh::LeanObject,
    mut v_inst_2233_: *mut leanh::LeanObject,
    mut v_nss_2234_: *mut leanh::LeanObject,
    mut v_idStx_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2236_ = leanh::lean_ctor_get(v_inst_2225_, 0);
    v_toBind_2237_ = leanh::lean_ctor_get(v_inst_2225_, 1);
    leanh::lean_inc_n(v_toBind_2237_, 3);
    v_toPure_2238_ = leanh::lean_ctor_get(v_toApplicative_2236_, 1);
    v___f_2239_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0;
    v___x_2240_ = leanh::lean_unsigned_to_nat(0);
    v___x_2241_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2;
    leanh::lean_inc_n(v_toPure_2238_, 3);
    v___f_2242_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2242_, 0, v_toPure_2238_);
    leanh::lean_inc(v_idStx_2235_);
    leanh::lean_inc_ref(v_inst_2231_);
    leanh::lean_inc(v_inst_2229_);
    leanh::lean_inc_ref(v_inst_2228_);
    leanh::lean_inc_ref_n(v_inst_2225_, 2);
    leanh::lean_inc_ref(v_inst_2227_);
    v___f_2243_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4
            as *mut core::ffi::c_void,
        16,
        13,
    );
    leanh::lean_closure_set(v___f_2243_, 0, v_inst_2227_);
    leanh::lean_closure_set(v___f_2243_, 1, v_toPure_2238_);
    leanh::lean_closure_set(v___f_2243_, 2, v_inst_2225_);
    leanh::lean_closure_set(v___f_2243_, 3, v_inst_2226_);
    leanh::lean_closure_set(v___f_2243_, 4, v_inst_2228_);
    leanh::lean_closure_set(v___f_2243_, 5, v_inst_2229_);
    leanh::lean_closure_set(v___f_2243_, 6, v_inst_2230_);
    leanh::lean_closure_set(v___f_2243_, 7, v_inst_2231_);
    leanh::lean_closure_set(v___f_2243_, 8, v_inst_2232_);
    leanh::lean_closure_set(v___f_2243_, 9, v_inst_2233_);
    leanh::lean_closure_set(v___f_2243_, 10, v_idStx_2235_);
    leanh::lean_closure_set(v___f_2243_, 11, v_toBind_2237_);
    leanh::lean_closure_set(v___f_2243_, 12, v___f_2242_);
    leanh::lean_inc(v_nss_2234_);
    v___f_2244_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2244_, 0, v_inst_2227_);
    leanh::lean_closure_set(v___f_2244_, 1, v_inst_2228_);
    leanh::lean_closure_set(v___f_2244_, 2, v_inst_2229_);
    leanh::lean_closure_set(v___f_2244_, 3, v_idStx_2235_);
    leanh::lean_closure_set(v___f_2244_, 4, v___f_2239_);
    leanh::lean_closure_set(v___f_2244_, 5, v_inst_2225_);
    leanh::lean_closure_set(v___f_2244_, 6, v_toBind_2237_);
    leanh::lean_closure_set(v___f_2244_, 7, v___x_2240_);
    leanh::lean_closure_set(v___f_2244_, 8, v_toPure_2238_);
    leanh::lean_closure_set(v___f_2244_, 9, v_nss_2234_);
    leanh::lean_closure_set(v___f_2244_, 10, v_inst_2231_);
    v___x_2245_ =
        l_List_forIn_x27_loop___redArg(v_inst_2225_, v___f_2243_, v_nss_2234_, v___x_2241_);
    leanh::lean_dec(v_nss_2234_);
    v___x_2246_ = leanh::lean_apply_4(
        v_toBind_2237_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2245_,
        v___f_2244_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(
    mut v_m_2247_: *mut leanh::LeanObject,
    mut v_inst_2248_: *mut leanh::LeanObject,
    mut v_inst_2249_: *mut leanh::LeanObject,
    mut v_inst_2250_: *mut leanh::LeanObject,
    mut v_inst_2251_: *mut leanh::LeanObject,
    mut v_inst_2252_: *mut leanh::LeanObject,
    mut v_inst_2253_: *mut leanh::LeanObject,
    mut v_inst_2254_: *mut leanh::LeanObject,
    mut v_inst_2255_: *mut leanh::LeanObject,
    mut v_inst_2256_: *mut leanh::LeanObject,
    mut v_nss_2257_: *mut leanh::LeanObject,
    mut v_idStx_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_openDecls_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_openDecls_2262_ = leanh::lean_ctor_get(v_a_2261_, 0);
    leanh::lean_inc(v_openDecls_2262_);
    leanh::lean_dec_ref(v_a_2261_);
    v_toPure_2263_ = leanh::lean_ctor_get(v_toApplicative_2260_, 1);
    leanh::lean_inc(v_toPure_2263_);
    leanh::lean_dec_ref(v_toApplicative_2260_);
    v___x_2264_ =
        leanh::lean_apply_2(v_toPure_2263_, leanh::lean_box(0), v_openDecls_2262_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
    mut v_inst_2265_: *mut leanh::LeanObject,
    mut v_toBind_2266_: *mut leanh::LeanObject,
    mut v___f_2267_: *mut leanh::LeanObject,
    mut v_____r_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2269_);
    v___x_2270_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2270_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2270_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2270_, 2, v___y_2269_);
    v___x_2271_ = leanh::lean_apply_2(v_inst_2265_, leanh::lean_box(0), v___x_2270_);
    v___x_2272_ = leanh::lean_apply_4(
        v_toBind_2266_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2271_,
        v___f_2267_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_toBind_2274_: *mut leanh::LeanObject,
    mut v___f_2275_: *mut leanh::LeanObject,
    mut v_____r_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
        v_inst_2273_,
        v_toBind_2274_,
        v___f_2275_,
        v_____r_2276_,
        v___y_2277_,
    );
    leanh::lean_dec(v___y_2277_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(
    mut v_x_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_2280_ = leanh::lean_ctor_get(v_x_2279_, 1);
    leanh::lean_inc(v_snd_2280_);
    return v_snd_2280_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(
    mut v_x_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_2281_);
    leanh::lean_dec_ref(v_x_2281_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(
    mut v_x_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2284_ = leanh::lean_ctor_get(v_x_2283_, 0);
    leanh::lean_inc(v_fst_2284_);
    return v_fst_2284_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(
    mut v_x_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_2285_);
    leanh::lean_dec_ref(v_x_2285_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(
    mut v_a_2287_: *mut leanh::LeanObject,
    mut v_toPure_2288_: *mut leanh::LeanObject,
    mut v_s_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2290_, 0, v_a_2287_);
    leanh::lean_ctor_set(v___x_2290_, 1, v_s_2289_);
    v___x_2291_ =
        leanh::lean_apply_2(v_toPure_2288_, leanh::lean_box(0), v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(
    mut v_toPure_2292_: *mut leanh::LeanObject,
    mut v_ref_2293_: *mut leanh::LeanObject,
    mut v_inst_2294_: *mut leanh::LeanObject,
    mut v_toBind_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2297_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2297_, 0, v_a_2296_);
    leanh::lean_closure_set(v___f_2297_, 1, v_toPure_2292_);
    v___x_2298_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2298_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2298_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2298_, 2, v_ref_2293_);
    v___x_2299_ = leanh::lean_apply_2(v_inst_2294_, leanh::lean_box(0), v___x_2298_);
    v___x_2300_ = leanh::lean_apply_4(
        v_toBind_2295_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2299_,
        v___f_2297_,
    );
    return v___x_2300_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(
    mut v___f_2301_: *mut leanh::LeanObject,
    mut v_ref_2302_: *mut leanh::LeanObject,
    mut v_a_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = leanh::lean_apply_2(v___f_2301_, v_a_2303_, v_ref_2302_);
    return v___x_2304_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(
    mut v___f_2305_: *mut leanh::LeanObject,
    mut v_ref_2306_: *mut leanh::LeanObject,
    mut v_a_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = leanh::lean_box(0);
    v___x_2309_ = leanh::lean_apply_2(v___f_2305_, v___x_2308_, v_ref_2306_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
    mut v___x_2311_: *mut leanh::LeanObject,
    mut v___x_2312_: *mut leanh::LeanObject,
    mut v___x_2313_: *mut leanh::LeanObject,
    mut v___x_2314_: *mut leanh::LeanObject,
    mut v___x_2315_: *mut leanh::LeanObject,
    mut v_x_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    v___x_2317_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0;
    v___x_2318_ = l_Lean_Name_mkStr4(v___x_2311_, v___x_2312_, v___x_2313_, v___x_2317_);
    leanh::lean_inc(v_x_2316_);
    v___x_2319_ = l_Lean_Syntax_isOfKind(v_x_2316_, v___x_2318_);
    leanh::lean_dec(v___x_2318_);
    if v___x_2319_ == 0 {
        let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2316_);
        v___x_2320_ = leanh::lean_box(0);
        return v___x_2320_;
    } else {
        let mut v_froms_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tos_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_froms_2321_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2314_);
        v_tos_2322_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2315_);
        leanh::lean_dec(v_x_2316_);
        v___x_2323_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2323_, 0, v_froms_2321_);
        leanh::lean_ctor_set(v___x_2323_, 1, v_tos_2322_);
        v___x_2324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2324_, 0, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(
    mut v___x_2325_: *mut leanh::LeanObject,
    mut v___x_2326_: *mut leanh::LeanObject,
    mut v___x_2327_: *mut leanh::LeanObject,
    mut v___x_2328_: *mut leanh::LeanObject,
    mut v___x_2329_: *mut leanh::LeanObject,
    mut v_x_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
        v___x_2325_,
        v___x_2326_,
        v___x_2327_,
        v___x_2328_,
        v___x_2329_,
        v_x_2330_,
    );
    leanh::lean_dec(v___x_2329_);
    leanh::lean_dec(v___x_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(
    mut v___x_2332_: *mut leanh::LeanObject,
    mut v_toPure_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2335_, 0, v___x_2332_);
    v___x_2336_ =
        leanh::lean_apply_2(v_toPure_2333_, leanh::lean_box(0), v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
    mut v_snd_2337_: *mut leanh::LeanObject,
    mut v_a_2338_: *mut leanh::LeanObject,
    mut v_inst_2339_: *mut leanh::LeanObject,
    mut v_toBind_2340_: *mut leanh::LeanObject,
    mut v___f_2341_: *mut leanh::LeanObject,
    mut v_____r_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Syntax_getId(v_snd_2337_);
    v___x_2345_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    leanh::lean_ctor_set(v___x_2345_, 1, v_a_2338_);
    v___x_2346_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2339_,
        v___x_2345_,
        v___y_2343_,
    );
    v___x_2347_ = leanh::lean_apply_4(
        v_toBind_2340_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2346_,
        v___f_2341_,
    );
    return v___x_2347_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(
    mut v_snd_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_toBind_2351_: *mut leanh::LeanObject,
    mut v___f_2352_: *mut leanh::LeanObject,
    mut v_____r_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
        v_snd_2348_,
        v_a_2349_,
        v_inst_2350_,
        v_toBind_2351_,
        v___f_2352_,
        v_____r_2353_,
        v___y_2354_,
    );
    leanh::lean_dec(v___y_2354_);
    leanh::lean_dec(v_snd_2348_);
    return v_res_2355_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(
    mut v___f_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v_a_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2357_);
    v___x_2359_ = leanh::lean_apply_2(v___f_2356_, v_a_2358_, v___y_2357_);
    return v___x_2359_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(
    mut v___f_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v_a_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2363_ =
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v___f_2360_, v___y_2361_, v_a_2362_);
    leanh::lean_dec(v___y_2361_);
    return v_res_2363_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(
    mut v___x_2364_: *mut leanh::LeanObject,
    mut v___x_2365_: *mut leanh::LeanObject,
    mut v___x_2366_: *mut leanh::LeanObject,
    mut v___x_2367_: *mut leanh::LeanObject,
    mut v_snd_2368_: *mut leanh::LeanObject,
    mut v_a_2369_: *mut leanh::LeanObject,
    mut v___x_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v_toBind_2372_: *mut leanh::LeanObject,
    mut v___f_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6682__overap_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6682__overap_2375_ = l_Lean_Elab_addConstInfo___redArg(
        v___x_2364_,
        v___x_2365_,
        v___x_2366_,
        v___x_2367_,
        v_snd_2368_,
        v_a_2369_,
        v___x_2370_,
    );
    leanh::lean_inc(v___y_2371_);
    v___x_2376_ = leanh::lean_apply_1(v___x_6682__overap_2375_, v___y_2371_);
    v___x_2377_ = leanh::lean_apply_4(
        v_toBind_2372_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2376_,
        v___f_2373_,
    );
    return v___x_2377_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(
    mut v___x_2378_: *mut leanh::LeanObject,
    mut v___x_2379_: *mut leanh::LeanObject,
    mut v___x_2380_: *mut leanh::LeanObject,
    mut v___x_2381_: *mut leanh::LeanObject,
    mut v_snd_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
    mut v___x_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
    mut v_toBind_2386_: *mut leanh::LeanObject,
    mut v___f_2387_: *mut leanh::LeanObject,
    mut v_a_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2385_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(
    mut v___f_2390_: *mut leanh::LeanObject,
    mut v___x_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___x_2393_: *mut leanh::LeanObject,
    mut v___x_2394_: *mut leanh::LeanObject,
    mut v___x_2395_: *mut leanh::LeanObject,
    mut v___x_2396_: *mut leanh::LeanObject,
    mut v_snd_2397_: *mut leanh::LeanObject,
    mut v_a_2398_: *mut leanh::LeanObject,
    mut v_toBind_2399_: *mut leanh::LeanObject,
    mut v___f_2400_: *mut leanh::LeanObject,
    mut v_fst_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enabled_2403_: u8 = 0;
    v_enabled_2403_ = leanh::lean_ctor_get_uint8(
        v_a_2402_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2403_ == 0 {
        let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_2401_);
        leanh::lean_dec(v___f_2400_);
        leanh::lean_dec(v_toBind_2399_);
        leanh::lean_dec(v_a_2398_);
        leanh::lean_dec(v_snd_2397_);
        leanh::lean_dec_ref(v___x_2396_);
        leanh::lean_dec_ref(v___x_2395_);
        leanh::lean_dec_ref(v___x_2394_);
        leanh::lean_dec_ref(v___x_2393_);
        leanh::lean_inc(v___y_2392_);
        v___x_2404_ = leanh::lean_apply_2(v___f_2390_, v___x_2391_, v___y_2392_);
        return v___x_2404_;
    } else {
        let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6697__overap_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2390_);
        v___x_2405_ = leanh::lean_box(0);
        leanh::lean_inc(v_toBind_2399_);
        leanh::lean_inc_n(v___y_2392_, 2);
        leanh::lean_inc(v_a_2398_);
        leanh::lean_inc_ref(v___x_2396_);
        leanh::lean_inc_ref(v___x_2395_);
        leanh::lean_inc_ref(v___x_2394_);
        leanh::lean_inc_ref(v___x_2393_);
        v___f_2406_ = leanh::lean_alloc_closure(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed as *mut core::ffi::c_void,
            11,
            10,
        );
        leanh::lean_closure_set(v___f_2406_, 0, v___x_2393_);
        leanh::lean_closure_set(v___f_2406_, 1, v___x_2394_);
        leanh::lean_closure_set(v___f_2406_, 2, v___x_2395_);
        leanh::lean_closure_set(v___f_2406_, 3, v___x_2396_);
        leanh::lean_closure_set(v___f_2406_, 4, v_snd_2397_);
        leanh::lean_closure_set(v___f_2406_, 5, v_a_2398_);
        leanh::lean_closure_set(v___f_2406_, 6, v___x_2405_);
        leanh::lean_closure_set(v___f_2406_, 7, v___y_2392_);
        leanh::lean_closure_set(v___f_2406_, 8, v_toBind_2399_);
        leanh::lean_closure_set(v___f_2406_, 9, v___f_2400_);
        v___x_6697__overap_2407_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2393_,
            v___x_2394_,
            v___x_2395_,
            v___x_2396_,
            v_fst_2401_,
            v_a_2398_,
            v___x_2405_,
        );
        v___x_2408_ = leanh::lean_apply_1(v___x_6697__overap_2407_, v___y_2392_);
        v___x_2409_ = leanh::lean_apply_4(
            v_toBind_2399_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2408_,
            v___f_2406_,
        );
        return v___x_2409_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(
    mut v___f_2410_: *mut leanh::LeanObject,
    mut v___x_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
    mut v___x_2413_: *mut leanh::LeanObject,
    mut v___x_2414_: *mut leanh::LeanObject,
    mut v___x_2415_: *mut leanh::LeanObject,
    mut v___x_2416_: *mut leanh::LeanObject,
    mut v_snd_2417_: *mut leanh::LeanObject,
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_toBind_2419_: *mut leanh::LeanObject,
    mut v___f_2420_: *mut leanh::LeanObject,
    mut v_fst_2421_: *mut leanh::LeanObject,
    mut v_a_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_a_2422_);
    leanh::lean_dec(v___y_2412_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(
    mut v___x_2424_: *mut leanh::LeanObject,
    mut v_inst_2425_: *mut leanh::LeanObject,
    mut v_snd_2426_: *mut leanh::LeanObject,
    mut v_inst_2427_: *mut leanh::LeanObject,
    mut v_toBind_2428_: *mut leanh::LeanObject,
    mut v___f_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___x_2431_: *mut leanh::LeanObject,
    mut v___x_2432_: *mut leanh::LeanObject,
    mut v___x_2433_: *mut leanh::LeanObject,
    mut v___x_2434_: *mut leanh::LeanObject,
    mut v_fst_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2425_);
    v___x_2437_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2424_, v_inst_2425_);
    v_getInfoState_2438_ = leanh::lean_ctor_get(v_inst_2425_, 0);
    leanh::lean_inc(v_getInfoState_2438_);
    leanh::lean_dec_ref(v_inst_2425_);
    leanh::lean_inc_n(v_toBind_2428_, 2);
    leanh::lean_inc(v_a_2436_);
    leanh::lean_inc(v_snd_2426_);
    v___f_2439_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_2439_, 0, v_snd_2426_);
    leanh::lean_closure_set(v___f_2439_, 1, v_a_2436_);
    leanh::lean_closure_set(v___f_2439_, 2, v_inst_2427_);
    leanh::lean_closure_set(v___f_2439_, 3, v_toBind_2428_);
    leanh::lean_closure_set(v___f_2439_, 4, v___f_2429_);
    leanh::lean_inc_n(v___y_2430_, 2);
    leanh::lean_inc_ref(v___f_2439_);
    v___f_2440_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2440_, 0, v___f_2439_);
    leanh::lean_closure_set(v___f_2440_, 1, v___y_2430_);
    v___f_2441_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_2441_, 0, v___f_2439_);
    leanh::lean_closure_set(v___f_2441_, 1, v___x_2431_);
    leanh::lean_closure_set(v___f_2441_, 2, v___y_2430_);
    leanh::lean_closure_set(v___f_2441_, 3, v___x_2432_);
    leanh::lean_closure_set(v___f_2441_, 4, v___x_2437_);
    leanh::lean_closure_set(v___f_2441_, 5, v___x_2433_);
    leanh::lean_closure_set(v___f_2441_, 6, v___x_2434_);
    leanh::lean_closure_set(v___f_2441_, 7, v_snd_2426_);
    leanh::lean_closure_set(v___f_2441_, 8, v_a_2436_);
    leanh::lean_closure_set(v___f_2441_, 9, v_toBind_2428_);
    leanh::lean_closure_set(v___f_2441_, 10, v___f_2440_);
    leanh::lean_closure_set(v___f_2441_, 11, v_fst_2435_);
    v___x_2442_ = leanh::lean_apply_4(
        v_toBind_2428_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getInfoState_2438_,
        v___f_2441_,
    );
    return v___x_2442_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(
    mut v___x_2443_: *mut leanh::LeanObject,
    mut v_inst_2444_: *mut leanh::LeanObject,
    mut v_snd_2445_: *mut leanh::LeanObject,
    mut v_inst_2446_: *mut leanh::LeanObject,
    mut v_toBind_2447_: *mut leanh::LeanObject,
    mut v___f_2448_: *mut leanh::LeanObject,
    mut v___y_2449_: *mut leanh::LeanObject,
    mut v___x_2450_: *mut leanh::LeanObject,
    mut v___x_2451_: *mut leanh::LeanObject,
    mut v___x_2452_: *mut leanh::LeanObject,
    mut v___x_2453_: *mut leanh::LeanObject,
    mut v_fst_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2449_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(
    mut v___x_2457_: *mut leanh::LeanObject,
    mut v_inst_2458_: *mut leanh::LeanObject,
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_toBind_2460_: *mut leanh::LeanObject,
    mut v___f_2461_: *mut leanh::LeanObject,
    mut v___x_2462_: *mut leanh::LeanObject,
    mut v___x_2463_: *mut leanh::LeanObject,
    mut v___x_2464_: *mut leanh::LeanObject,
    mut v___x_2465_: *mut leanh::LeanObject,
    mut v_inst_2466_: *mut leanh::LeanObject,
    mut v_inst_2467_: *mut leanh::LeanObject,
    mut v___x_2468_: *mut leanh::LeanObject,
    mut v___x_2469_: *mut leanh::LeanObject,
    mut v___x_2470_: *mut leanh::LeanObject,
    mut v___f_2471_: *mut leanh::LeanObject,
    mut v___x_2472_: *mut leanh::LeanObject,
    mut v_a_2473_: *mut leanh::LeanObject,
    mut v_a_2474_: *mut leanh::LeanObject,
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738__overap_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2478_ = leanh::lean_ctor_get(v_a_2474_, 0);
    leanh::lean_inc_n(v_fst_2478_, 2);
    v_snd_2479_ = leanh::lean_ctor_get(v_a_2474_, 1);
    leanh::lean_inc(v_snd_2479_);
    leanh::lean_dec_ref(v_a_2474_);
    leanh::lean_inc_ref(v___x_2464_);
    leanh::lean_inc_ref(v___x_2463_);
    leanh::lean_inc_n(v___y_2477_, 2);
    leanh::lean_inc(v_toBind_2460_);
    leanh::lean_inc(v___x_2457_);
    v___f_2480_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_2480_, 0, v___x_2457_);
    leanh::lean_closure_set(v___f_2480_, 1, v_inst_2458_);
    leanh::lean_closure_set(v___f_2480_, 2, v_snd_2479_);
    leanh::lean_closure_set(v___f_2480_, 3, v_inst_2459_);
    leanh::lean_closure_set(v___f_2480_, 4, v_toBind_2460_);
    leanh::lean_closure_set(v___f_2480_, 5, v___f_2461_);
    leanh::lean_closure_set(v___f_2480_, 6, v___y_2477_);
    leanh::lean_closure_set(v___f_2480_, 7, v___x_2462_);
    leanh::lean_closure_set(v___f_2480_, 8, v___x_2463_);
    leanh::lean_closure_set(v___f_2480_, 9, v___x_2464_);
    leanh::lean_closure_set(v___f_2480_, 10, v___x_2465_);
    leanh::lean_closure_set(v___f_2480_, 11, v_fst_2478_);
    v___x_2481_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2457_, v_inst_2466_);
    v___x_2482_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_2482_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2482_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2482_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2482_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2482_, 4, v_inst_2467_);
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
    v___x_2484_ = leanh::lean_apply_1(v___x_6738__overap_2483_, v___y_2477_);
    v___x_2485_ = leanh::lean_apply_4(
        v_toBind_2460_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2484_,
        v___f_2480_,
    );
    return v___x_2485_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_2487_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_2488_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toBind_2489_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_2490_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2491_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2492_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2493_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2494_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2495_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_2496_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2497_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2498_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2499_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_2500_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_2501_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_2502_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_2503_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_x_2504_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2505_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_2506_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_res_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2506_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(
    mut v_froms_2508_: *mut leanh::LeanObject,
    mut v_tos_2509_: *mut leanh::LeanObject,
    mut v_toPure_2510_: *mut leanh::LeanObject,
    mut v___x_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
    mut v_toBind_2514_: *mut leanh::LeanObject,
    mut v___x_2515_: *mut leanh::LeanObject,
    mut v___x_2516_: *mut leanh::LeanObject,
    mut v___x_2517_: *mut leanh::LeanObject,
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v___x_2520_: *mut leanh::LeanObject,
    mut v___x_2521_: *mut leanh::LeanObject,
    mut v___x_2522_: *mut leanh::LeanObject,
    mut v___f_2523_: *mut leanh::LeanObject,
    mut v___x_2524_: *mut leanh::LeanObject,
    mut v___x_2525_: usize,
    mut v_ref_2526_: *mut leanh::LeanObject,
    mut v___f_2527_: *mut leanh::LeanObject,
    mut v_a_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2533_: usize = 0;
    let mut v___x_6759__overap_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Array_zip___redArg(v_froms_2508_, v_tos_2509_);
    v___x_2530_ = leanh::lean_box(0);
    v___f_2531_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2531_, 0, v___x_2530_);
    leanh::lean_closure_set(v___f_2531_, 1, v_toPure_2510_);
    leanh::lean_inc_ref(v___x_2515_);
    leanh::lean_inc(v_toBind_2514_);
    v___f_2532_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    leanh::lean_closure_set(v___f_2532_, 0, v___x_2511_);
    leanh::lean_closure_set(v___f_2532_, 1, v_inst_2512_);
    leanh::lean_closure_set(v___f_2532_, 2, v_inst_2513_);
    leanh::lean_closure_set(v___f_2532_, 3, v_toBind_2514_);
    leanh::lean_closure_set(v___f_2532_, 4, v___f_2531_);
    leanh::lean_closure_set(v___f_2532_, 5, v___x_2530_);
    leanh::lean_closure_set(v___f_2532_, 6, v___x_2515_);
    leanh::lean_closure_set(v___f_2532_, 7, v___x_2516_);
    leanh::lean_closure_set(v___f_2532_, 8, v___x_2517_);
    leanh::lean_closure_set(v___f_2532_, 9, v_inst_2518_);
    leanh::lean_closure_set(v___f_2532_, 10, v_inst_2519_);
    leanh::lean_closure_set(v___f_2532_, 11, v___x_2520_);
    leanh::lean_closure_set(v___f_2532_, 12, v___x_2521_);
    leanh::lean_closure_set(v___f_2532_, 13, v___x_2522_);
    leanh::lean_closure_set(v___f_2532_, 14, v___f_2523_);
    leanh::lean_closure_set(v___f_2532_, 15, v___x_2524_);
    leanh::lean_closure_set(v___f_2532_, 16, v_a_2528_);
    v_sz_2533_ = lean_array_size(v___x_2529_);
    v___x_6759__overap_2534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2515_,
        v___x_2529_,
        v___f_2532_,
        v_sz_2533_,
        v___x_2525_,
        v___x_2530_,
    );
    v___x_2535_ = leanh::lean_apply_1(v___x_6759__overap_2534_, v_ref_2526_);
    v___x_2536_ = leanh::lean_apply_4(
        v_toBind_2514_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2535_,
        v___f_2527_,
    );
    return v___x_2536_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_froms_2537_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_tos_2538_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_toPure_2539_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_2540_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_2541_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_2542_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2543_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2544_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2545_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2546_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_2547_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_2548_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2549_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2550_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2551_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___f_2552_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___x_2553_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_2554_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_ref_2555_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___f_2556_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_a_2557_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___x_7638__boxed_2558_: usize = 0;
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7638__boxed_2558_ = leanh::lean_unbox_usize(v___x_2554_);
    leanh::lean_dec(v___x_2554_);
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
    leanh::lean_dec_ref(v_tos_2538_);
    leanh::lean_dec_ref(v_froms_2537_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
    mut v___x_2560_: u8,
    mut v___x_2561_: u8,
    mut v_x1_2562_: *mut leanh::LeanObject,
    mut v_x2_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v_snd_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v_unused_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_unused_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2564_ = leanh::lean_ctor_get(v_x1_2562_, 0);
                v___x_2565_ = (leanh::lean_unbox(v_fst_2564_) as u8);
                if v___x_2565_ == 0 {
                    leanh::lean_dec(v_x2_2563_);
                    v_snd_2566_ = leanh::lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2574_ = (!leanh::lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2574_ == 0 {
                        v_unused_2575_ = leanh::lean_ctor_get(v_x1_2562_, 0);
                        leanh::lean_dec(v_unused_2575_);
                        v___x_2568_ = v_x1_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2566_);
                        leanh::lean_dec(v_x1_2562_);
                        v___x_2568_ = leanh::lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2576_ = leanh::lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2585_ = (!leanh::lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2585_ == 0 {
                        v_unused_2586_ = leanh::lean_ctor_get(v_x1_2562_, 0);
                        leanh::lean_dec(v_unused_2586_);
                        v___x_2578_ = v_x1_2562_;
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2576_);
                        leanh::lean_dec(v_x1_2562_);
                        v___x_2578_ = leanh::lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2570_ = leanh::lean_box((v___x_2560_) as usize);
                if v_isShared_2569_ == 0 {
                    leanh::lean_ctor_set(v___x_2568_, 0, v___x_2570_);
                    v___x_2572_ = v___x_2568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_snd_2566_);
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
                v___x_2581_ = leanh::lean_box((v___x_2561_) as usize);
                if v_isShared_2579_ == 0 {
                    leanh::lean_ctor_set(v___x_2578_, 1, v___x_2580_);
                    leanh::lean_ctor_set(v___x_2578_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2580_);
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
    mut v___x_2587_: *mut leanh::LeanObject,
    mut v___x_2588_: *mut leanh::LeanObject,
    mut v_x1_2589_: *mut leanh::LeanObject,
    mut v_x2_2590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7682__boxed_2591_: u8 = 0;
    let mut v___x_7683__boxed_2592_: u8 = 0;
    let mut v_res_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7682__boxed_2591_ = (leanh::lean_unbox(v___x_2587_) as u8);
    v___x_7683__boxed_2592_ = (leanh::lean_unbox(v___x_2588_) as u8);
    v_res_2593_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
        v___x_7682__boxed_2591_,
        v___x_7683__boxed_2592_,
        v_x1_2589_,
        v_x2_2590_,
    );
    return v_res_2593_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(
    mut v_ids_2594_: *mut leanh::LeanObject,
    mut v___f_2595_: *mut leanh::LeanObject,
    mut v_a_2596_: *mut leanh::LeanObject,
    mut v_inst_2597_: *mut leanh::LeanObject,
    mut v_ref_2598_: *mut leanh::LeanObject,
    mut v_toBind_2599_: *mut leanh::LeanObject,
    mut v___f_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
    v_sz_2603_ = lean_array_size(v_ids_2594_);
    v___x_2604_ = 0usize;
    v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2602_,
        v___f_2595_,
        v_sz_2603_,
        v___x_2604_,
        v_ids_2594_,
    );
    v___x_2606_ = lean_array_to_list(v___x_2605_);
    v___x_2607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2607_, 0, v_a_2596_);
    leanh::lean_ctor_set(v___x_2607_, 1, v___x_2606_);
    v___x_2608_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2597_,
        v___x_2607_,
        v_ref_2598_,
    );
    v___x_2609_ = leanh::lean_apply_4(
        v_toBind_2599_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2608_,
        v___f_2600_,
    );
    return v___x_2609_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(
    mut v_ids_2610_: *mut leanh::LeanObject,
    mut v___f_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
    mut v_inst_2613_: *mut leanh::LeanObject,
    mut v_ref_2614_: *mut leanh::LeanObject,
    mut v_toBind_2615_: *mut leanh::LeanObject,
    mut v___f_2616_: *mut leanh::LeanObject,
    mut v_a_2617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_ref_2614_);
    return v_res_2618_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(
    mut v___x_2619_: *mut leanh::LeanObject,
    mut v_toPure_2620_: *mut leanh::LeanObject,
    mut v___x_2621_: *mut leanh::LeanObject,
    mut v___x_2622_: *mut leanh::LeanObject,
    mut v___x_2623_: *mut leanh::LeanObject,
    mut v___x_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_a_2626_: *mut leanh::LeanObject,
    mut v___y_2627_: *mut leanh::LeanObject,
    mut v_toBind_2628_: *mut leanh::LeanObject,
    mut v___f_2629_: *mut leanh::LeanObject,
    mut v_a_2630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enabled_2631_: u8 = 0;
    v_enabled_2631_ = leanh::lean_ctor_get_uint8(
        v_a_2630_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2631_ == 0 {
        let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2629_);
        leanh::lean_dec(v_toBind_2628_);
        leanh::lean_dec(v_a_2626_);
        leanh::lean_dec(v_a_2625_);
        leanh::lean_dec_ref(v___x_2624_);
        leanh::lean_dec_ref(v___x_2623_);
        leanh::lean_dec_ref(v___x_2622_);
        leanh::lean_dec_ref(v___x_2621_);
        v___x_2632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2632_, 0, v___x_2619_);
        v___x_2633_ =
            leanh::lean_apply_2(v_toPure_2620_, leanh::lean_box(0), v___x_2632_);
        return v___x_2633_;
    } else {
        let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6804__overap_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2620_);
        v___x_2634_ = leanh::lean_box(0);
        v___x_6804__overap_2635_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2621_,
            v___x_2622_,
            v___x_2623_,
            v___x_2624_,
            v_a_2625_,
            v_a_2626_,
            v___x_2634_,
        );
        leanh::lean_inc(v___y_2627_);
        v___x_2636_ = leanh::lean_apply_1(v___x_6804__overap_2635_, v___y_2627_);
        v___x_2637_ = leanh::lean_apply_4(
            v_toBind_2628_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2636_,
            v___f_2629_,
        );
        return v___x_2637_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(
    mut v___x_2638_: *mut leanh::LeanObject,
    mut v_toPure_2639_: *mut leanh::LeanObject,
    mut v___x_2640_: *mut leanh::LeanObject,
    mut v___x_2641_: *mut leanh::LeanObject,
    mut v___x_2642_: *mut leanh::LeanObject,
    mut v___x_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v_toBind_2647_: *mut leanh::LeanObject,
    mut v___f_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_a_2649_);
    leanh::lean_dec(v___y_2646_);
    return v_res_2650_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(
    mut v___x_2651_: *mut leanh::LeanObject,
    mut v_inst_2652_: *mut leanh::LeanObject,
    mut v___x_2653_: *mut leanh::LeanObject,
    mut v_toPure_2654_: *mut leanh::LeanObject,
    mut v___x_2655_: *mut leanh::LeanObject,
    mut v___x_2656_: *mut leanh::LeanObject,
    mut v___x_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v_toBind_2660_: *mut leanh::LeanObject,
    mut v___f_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2652_);
    v___x_2663_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2651_, v_inst_2652_);
    v_getInfoState_2664_ = leanh::lean_ctor_get(v_inst_2652_, 0);
    leanh::lean_inc(v_getInfoState_2664_);
    leanh::lean_dec_ref(v_inst_2652_);
    leanh::lean_inc(v_toBind_2660_);
    leanh::lean_inc(v___y_2659_);
    v___f_2665_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2665_, 0, v___x_2653_);
    leanh::lean_closure_set(v___f_2665_, 1, v_toPure_2654_);
    leanh::lean_closure_set(v___f_2665_, 2, v___x_2655_);
    leanh::lean_closure_set(v___f_2665_, 3, v___x_2663_);
    leanh::lean_closure_set(v___f_2665_, 4, v___x_2656_);
    leanh::lean_closure_set(v___f_2665_, 5, v___x_2657_);
    leanh::lean_closure_set(v___f_2665_, 6, v_a_2658_);
    leanh::lean_closure_set(v___f_2665_, 7, v_a_2662_);
    leanh::lean_closure_set(v___f_2665_, 8, v___y_2659_);
    leanh::lean_closure_set(v___f_2665_, 9, v_toBind_2660_);
    leanh::lean_closure_set(v___f_2665_, 10, v___f_2661_);
    v___x_2666_ = leanh::lean_apply_4(
        v_toBind_2660_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getInfoState_2664_,
        v___f_2665_,
    );
    return v___x_2666_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(
    mut v___x_2667_: *mut leanh::LeanObject,
    mut v_inst_2668_: *mut leanh::LeanObject,
    mut v___x_2669_: *mut leanh::LeanObject,
    mut v_toPure_2670_: *mut leanh::LeanObject,
    mut v___x_2671_: *mut leanh::LeanObject,
    mut v___x_2672_: *mut leanh::LeanObject,
    mut v___x_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v_toBind_2676_: *mut leanh::LeanObject,
    mut v___f_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2675_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(
    mut v___x_2680_: *mut leanh::LeanObject,
    mut v_inst_2681_: *mut leanh::LeanObject,
    mut v___x_2682_: *mut leanh::LeanObject,
    mut v_toPure_2683_: *mut leanh::LeanObject,
    mut v___x_2684_: *mut leanh::LeanObject,
    mut v___x_2685_: *mut leanh::LeanObject,
    mut v___x_2686_: *mut leanh::LeanObject,
    mut v_toBind_2687_: *mut leanh::LeanObject,
    mut v___f_2688_: *mut leanh::LeanObject,
    mut v_inst_2689_: *mut leanh::LeanObject,
    mut v_inst_2690_: *mut leanh::LeanObject,
    mut v___x_2691_: *mut leanh::LeanObject,
    mut v___x_2692_: *mut leanh::LeanObject,
    mut v___x_2693_: *mut leanh::LeanObject,
    mut v___f_2694_: *mut leanh::LeanObject,
    mut v___x_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_x_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837__overap_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2687_);
    leanh::lean_inc_n(v___y_2700_, 2);
    leanh::lean_inc(v_a_2697_);
    leanh::lean_inc_ref(v___x_2685_);
    leanh::lean_inc_ref(v___x_2684_);
    leanh::lean_inc(v___x_2680_);
    v___f_2701_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2701_, 0, v___x_2680_);
    leanh::lean_closure_set(v___f_2701_, 1, v_inst_2681_);
    leanh::lean_closure_set(v___f_2701_, 2, v___x_2682_);
    leanh::lean_closure_set(v___f_2701_, 3, v_toPure_2683_);
    leanh::lean_closure_set(v___f_2701_, 4, v___x_2684_);
    leanh::lean_closure_set(v___f_2701_, 5, v___x_2685_);
    leanh::lean_closure_set(v___f_2701_, 6, v___x_2686_);
    leanh::lean_closure_set(v___f_2701_, 7, v_a_2697_);
    leanh::lean_closure_set(v___f_2701_, 8, v___y_2700_);
    leanh::lean_closure_set(v___f_2701_, 9, v_toBind_2687_);
    leanh::lean_closure_set(v___f_2701_, 10, v___f_2688_);
    v___x_2702_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2680_, v_inst_2689_);
    v___x_2703_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_2703_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2703_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2703_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2703_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2703_, 4, v_inst_2690_);
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
    v___x_2705_ = leanh::lean_apply_1(v___x_6837__overap_2704_, v___y_2700_);
    v___x_2706_ = leanh::lean_apply_4(
        v_toBind_2687_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2705_,
        v___f_2701_,
    );
    return v___x_2706_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2707_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_2708_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_2709_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toPure_2710_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2711_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2712_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2713_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_toBind_2714_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_2715_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2716_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_2717_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2718_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2719_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2720_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_2721_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_2722_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_2723_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_2724_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_x_2725_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2726_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_2727_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_res_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2727_);
    return v_res_2728_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(
    mut v_toPure_2729_: *mut leanh::LeanObject,
    mut v___x_2730_: *mut leanh::LeanObject,
    mut v_inst_2731_: *mut leanh::LeanObject,
    mut v___x_2732_: *mut leanh::LeanObject,
    mut v___x_2733_: *mut leanh::LeanObject,
    mut v___x_2734_: *mut leanh::LeanObject,
    mut v_toBind_2735_: *mut leanh::LeanObject,
    mut v_inst_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v___x_2738_: *mut leanh::LeanObject,
    mut v___x_2739_: *mut leanh::LeanObject,
    mut v___x_2740_: *mut leanh::LeanObject,
    mut v___f_2741_: *mut leanh::LeanObject,
    mut v___x_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_ids_2744_: *mut leanh::LeanObject,
    mut v_ref_2745_: *mut leanh::LeanObject,
    mut v___f_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_6856__overap_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = leanh::lean_box(0);
    leanh::lean_inc(v_toPure_2729_);
    v___f_2749_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2749_, 0, v___x_2748_);
    leanh::lean_closure_set(v___f_2749_, 1, v_toPure_2729_);
    leanh::lean_inc(v_toBind_2735_);
    leanh::lean_inc_ref(v___x_2732_);
    v___f_2750_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    leanh::lean_closure_set(v___f_2750_, 0, v___x_2730_);
    leanh::lean_closure_set(v___f_2750_, 1, v_inst_2731_);
    leanh::lean_closure_set(v___f_2750_, 2, v___x_2748_);
    leanh::lean_closure_set(v___f_2750_, 3, v_toPure_2729_);
    leanh::lean_closure_set(v___f_2750_, 4, v___x_2732_);
    leanh::lean_closure_set(v___f_2750_, 5, v___x_2733_);
    leanh::lean_closure_set(v___f_2750_, 6, v___x_2734_);
    leanh::lean_closure_set(v___f_2750_, 7, v_toBind_2735_);
    leanh::lean_closure_set(v___f_2750_, 8, v___f_2749_);
    leanh::lean_closure_set(v___f_2750_, 9, v_inst_2736_);
    leanh::lean_closure_set(v___f_2750_, 10, v_inst_2737_);
    leanh::lean_closure_set(v___f_2750_, 11, v___x_2738_);
    leanh::lean_closure_set(v___f_2750_, 12, v___x_2739_);
    leanh::lean_closure_set(v___f_2750_, 13, v___x_2740_);
    leanh::lean_closure_set(v___f_2750_, 14, v___f_2741_);
    leanh::lean_closure_set(v___f_2750_, 15, v___x_2742_);
    leanh::lean_closure_set(v___f_2750_, 16, v_a_2743_);
    v_sz_2751_ = lean_array_size(v_ids_2744_);
    v___x_2752_ = 0usize;
    v___x_6856__overap_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2732_,
        v_ids_2744_,
        v___f_2750_,
        v_sz_2751_,
        v___x_2752_,
        v___x_2748_,
    );
    v___x_2754_ = leanh::lean_apply_1(v___x_6856__overap_2753_, v_ref_2745_);
    v___x_2755_ = leanh::lean_apply_4(
        v_toBind_2735_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2754_,
        v___f_2746_,
    );
    return v___x_2755_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_2756_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_2757_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_2758_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_2759_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2760_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2761_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2762_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_2763_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_2764_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2765_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_2766_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2767_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___f_2768_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2769_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_2770_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_ids_2771_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_ref_2772_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_2773_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_2774_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_ids_2776_: *mut leanh::LeanObject,
    mut v___f_2777_: *mut leanh::LeanObject,
    mut v_inst_2778_: *mut leanh::LeanObject,
    mut v_ref_2779_: *mut leanh::LeanObject,
    mut v_toBind_2780_: *mut leanh::LeanObject,
    mut v___f_2781_: *mut leanh::LeanObject,
    mut v_toPure_2782_: *mut leanh::LeanObject,
    mut v___x_2783_: *mut leanh::LeanObject,
    mut v_inst_2784_: *mut leanh::LeanObject,
    mut v___x_2785_: *mut leanh::LeanObject,
    mut v___x_2786_: *mut leanh::LeanObject,
    mut v___x_2787_: *mut leanh::LeanObject,
    mut v_inst_2788_: *mut leanh::LeanObject,
    mut v_inst_2789_: *mut leanh::LeanObject,
    mut v___x_2790_: *mut leanh::LeanObject,
    mut v___x_2791_: *mut leanh::LeanObject,
    mut v___x_2792_: *mut leanh::LeanObject,
    mut v___f_2793_: *mut leanh::LeanObject,
    mut v___x_2794_: *mut leanh::LeanObject,
    mut v_a_2795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876__overap_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_toBind_2780_, 2);
    leanh::lean_inc_n(v_ref_2779_, 2);
    leanh::lean_inc(v_inst_2778_);
    leanh::lean_inc_n(v_a_2795_, 2);
    leanh::lean_inc_ref(v_ids_2776_);
    v___f_2796_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2796_, 0, v_ids_2776_);
    leanh::lean_closure_set(v___f_2796_, 1, v___f_2777_);
    leanh::lean_closure_set(v___f_2796_, 2, v_a_2795_);
    leanh::lean_closure_set(v___f_2796_, 3, v_inst_2778_);
    leanh::lean_closure_set(v___f_2796_, 4, v_ref_2779_);
    leanh::lean_closure_set(v___f_2796_, 5, v_toBind_2780_);
    leanh::lean_closure_set(v___f_2796_, 6, v___f_2781_);
    leanh::lean_inc_ref(v___x_2786_);
    leanh::lean_inc_ref(v___x_2785_);
    leanh::lean_inc(v___x_2783_);
    v___f_2797_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    leanh::lean_closure_set(v___f_2797_, 0, v_toPure_2782_);
    leanh::lean_closure_set(v___f_2797_, 1, v___x_2783_);
    leanh::lean_closure_set(v___f_2797_, 2, v_inst_2784_);
    leanh::lean_closure_set(v___f_2797_, 3, v___x_2785_);
    leanh::lean_closure_set(v___f_2797_, 4, v___x_2786_);
    leanh::lean_closure_set(v___f_2797_, 5, v___x_2787_);
    leanh::lean_closure_set(v___f_2797_, 6, v_toBind_2780_);
    leanh::lean_closure_set(v___f_2797_, 7, v_inst_2788_);
    leanh::lean_closure_set(v___f_2797_, 8, v_inst_2789_);
    leanh::lean_closure_set(v___f_2797_, 9, v___x_2790_);
    leanh::lean_closure_set(v___f_2797_, 10, v___x_2791_);
    leanh::lean_closure_set(v___f_2797_, 11, v___x_2792_);
    leanh::lean_closure_set(v___f_2797_, 12, v___f_2793_);
    leanh::lean_closure_set(v___f_2797_, 13, v___x_2794_);
    leanh::lean_closure_set(v___f_2797_, 14, v_a_2795_);
    leanh::lean_closure_set(v___f_2797_, 15, v_ids_2776_);
    leanh::lean_closure_set(v___f_2797_, 16, v_ref_2779_);
    leanh::lean_closure_set(v___f_2797_, 17, v___f_2796_);
    v___f_2798_ = leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2798_, 0, v_inst_2778_);
    leanh::lean_closure_set(v___f_2798_, 1, v___x_2783_);
    v___x_6876__overap_2799_ =
        l_Lean_activateScoped___redArg(v___x_2785_, v___x_2786_, v___f_2798_, v_a_2795_);
    v___x_2800_ = leanh::lean_apply_1(v___x_6876__overap_2799_, v_ref_2779_);
    v___x_2801_ = leanh::lean_apply_4(
        v_toBind_2780_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2800_,
        v___f_2797_,
    );
    return v___x_2801_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ids_2802_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___f_2803_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_2804_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ref_2805_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_toBind_2806_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___f_2807_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toPure_2808_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2809_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_2810_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2811_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_2812_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2813_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_inst_2814_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_inst_2815_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2816_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_2817_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___x_2818_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_2819_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_2820_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_2821_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
    mut v_inst_2825_: *mut leanh::LeanObject,
    mut v_toBind_2826_: *mut leanh::LeanObject,
    mut v___f_2827_: *mut leanh::LeanObject,
    mut v_____r_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_TSyntax_getId(v_a_2823_);
    v___x_2831_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2831_, 0, v___x_2830_);
    leanh::lean_ctor_set(v___x_2831_, 1, v_a_2824_);
    v___x_2832_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2825_,
        v___x_2831_,
        v___y_2829_,
    );
    v___x_2833_ = leanh::lean_apply_4(
        v_toBind_2826_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2832_,
        v___f_2827_,
    );
    return v___x_2833_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(
    mut v_a_2834_: *mut leanh::LeanObject,
    mut v_a_2835_: *mut leanh::LeanObject,
    mut v_inst_2836_: *mut leanh::LeanObject,
    mut v_toBind_2837_: *mut leanh::LeanObject,
    mut v___f_2838_: *mut leanh::LeanObject,
    mut v_____r_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(
        v_a_2834_,
        v_a_2835_,
        v_inst_2836_,
        v_toBind_2837_,
        v___f_2838_,
        v_____r_2839_,
        v___y_2840_,
    );
    leanh::lean_dec(v___y_2840_);
    leanh::lean_dec(v_a_2834_);
    return v_res_2841_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(
    mut v___f_2842_: *mut leanh::LeanObject,
    mut v___x_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
    mut v___x_2845_: *mut leanh::LeanObject,
    mut v___x_2846_: *mut leanh::LeanObject,
    mut v___x_2847_: *mut leanh::LeanObject,
    mut v___x_2848_: *mut leanh::LeanObject,
    mut v_a_2849_: *mut leanh::LeanObject,
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_toBind_2851_: *mut leanh::LeanObject,
    mut v___f_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enabled_2854_: u8 = 0;
    v_enabled_2854_ = leanh::lean_ctor_get_uint8(
        v_a_2853_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    if v_enabled_2854_ == 0 {
        let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2852_);
        leanh::lean_dec(v_toBind_2851_);
        leanh::lean_dec(v_a_2850_);
        leanh::lean_dec(v_a_2849_);
        leanh::lean_dec_ref(v___x_2848_);
        leanh::lean_dec_ref(v___x_2847_);
        leanh::lean_dec_ref(v___x_2846_);
        leanh::lean_dec_ref(v___x_2845_);
        leanh::lean_inc(v___y_2844_);
        v___x_2855_ = leanh::lean_apply_2(v___f_2842_, v___x_2843_, v___y_2844_);
        return v___x_2855_;
    } else {
        let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6905__overap_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2842_);
        v___x_2856_ = leanh::lean_box(0);
        v___x_6905__overap_2857_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2845_,
            v___x_2846_,
            v___x_2847_,
            v___x_2848_,
            v_a_2849_,
            v_a_2850_,
            v___x_2856_,
        );
        leanh::lean_inc(v___y_2844_);
        v___x_2858_ = leanh::lean_apply_1(v___x_6905__overap_2857_, v___y_2844_);
        v___x_2859_ = leanh::lean_apply_4(
            v_toBind_2851_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2858_,
            v___f_2852_,
        );
        return v___x_2859_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(
    mut v___f_2860_: *mut leanh::LeanObject,
    mut v___x_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___x_2863_: *mut leanh::LeanObject,
    mut v___x_2864_: *mut leanh::LeanObject,
    mut v___x_2865_: *mut leanh::LeanObject,
    mut v___x_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_toBind_2869_: *mut leanh::LeanObject,
    mut v___f_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_a_2871_);
    leanh::lean_dec(v___y_2862_);
    return v_res_2872_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(
    mut v___x_2873_: *mut leanh::LeanObject,
    mut v_inst_2874_: *mut leanh::LeanObject,
    mut v_a_2875_: *mut leanh::LeanObject,
    mut v_inst_2876_: *mut leanh::LeanObject,
    mut v_toBind_2877_: *mut leanh::LeanObject,
    mut v___f_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___x_2880_: *mut leanh::LeanObject,
    mut v___x_2881_: *mut leanh::LeanObject,
    mut v___x_2882_: *mut leanh::LeanObject,
    mut v___x_2883_: *mut leanh::LeanObject,
    mut v_a_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2874_);
    v___x_2885_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2873_, v_inst_2874_);
    v_getInfoState_2886_ = leanh::lean_ctor_get(v_inst_2874_, 0);
    leanh::lean_inc(v_getInfoState_2886_);
    leanh::lean_dec_ref(v_inst_2874_);
    leanh::lean_inc_n(v_toBind_2877_, 2);
    leanh::lean_inc(v_a_2884_);
    leanh::lean_inc(v_a_2875_);
    v___f_2887_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_2887_, 0, v_a_2875_);
    leanh::lean_closure_set(v___f_2887_, 1, v_a_2884_);
    leanh::lean_closure_set(v___f_2887_, 2, v_inst_2876_);
    leanh::lean_closure_set(v___f_2887_, 3, v_toBind_2877_);
    leanh::lean_closure_set(v___f_2887_, 4, v___f_2878_);
    leanh::lean_inc_n(v___y_2879_, 2);
    leanh::lean_inc_ref(v___f_2887_);
    v___f_2888_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2888_, 0, v___f_2887_);
    leanh::lean_closure_set(v___f_2888_, 1, v___y_2879_);
    v___f_2889_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2889_, 0, v___f_2887_);
    leanh::lean_closure_set(v___f_2889_, 1, v___x_2880_);
    leanh::lean_closure_set(v___f_2889_, 2, v___y_2879_);
    leanh::lean_closure_set(v___f_2889_, 3, v___x_2881_);
    leanh::lean_closure_set(v___f_2889_, 4, v___x_2885_);
    leanh::lean_closure_set(v___f_2889_, 5, v___x_2882_);
    leanh::lean_closure_set(v___f_2889_, 6, v___x_2883_);
    leanh::lean_closure_set(v___f_2889_, 7, v_a_2875_);
    leanh::lean_closure_set(v___f_2889_, 8, v_a_2884_);
    leanh::lean_closure_set(v___f_2889_, 9, v_toBind_2877_);
    leanh::lean_closure_set(v___f_2889_, 10, v___f_2888_);
    v___x_2890_ = leanh::lean_apply_4(
        v_toBind_2877_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getInfoState_2886_,
        v___f_2889_,
    );
    return v___x_2890_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(
    mut v___x_2891_: *mut leanh::LeanObject,
    mut v_inst_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
    mut v_inst_2894_: *mut leanh::LeanObject,
    mut v_toBind_2895_: *mut leanh::LeanObject,
    mut v___f_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___x_2898_: *mut leanh::LeanObject,
    mut v___x_2899_: *mut leanh::LeanObject,
    mut v___x_2900_: *mut leanh::LeanObject,
    mut v___x_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2897_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(
    mut v___x_2904_: *mut leanh::LeanObject,
    mut v_inst_2905_: *mut leanh::LeanObject,
    mut v_inst_2906_: *mut leanh::LeanObject,
    mut v_toBind_2907_: *mut leanh::LeanObject,
    mut v___f_2908_: *mut leanh::LeanObject,
    mut v___x_2909_: *mut leanh::LeanObject,
    mut v___x_2910_: *mut leanh::LeanObject,
    mut v___x_2911_: *mut leanh::LeanObject,
    mut v___x_2912_: *mut leanh::LeanObject,
    mut v_inst_2913_: *mut leanh::LeanObject,
    mut v_inst_2914_: *mut leanh::LeanObject,
    mut v___x_2915_: *mut leanh::LeanObject,
    mut v___x_2916_: *mut leanh::LeanObject,
    mut v___x_2917_: *mut leanh::LeanObject,
    mut v___f_2918_: *mut leanh::LeanObject,
    mut v___x_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
    mut v_x_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942__overap_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v___x_2911_);
    leanh::lean_inc_ref(v___x_2910_);
    leanh::lean_inc_n(v___y_2924_, 2);
    leanh::lean_inc(v_toBind_2907_);
    leanh::lean_inc(v_a_2921_);
    leanh::lean_inc(v___x_2904_);
    v___f_2925_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2925_, 0, v___x_2904_);
    leanh::lean_closure_set(v___f_2925_, 1, v_inst_2905_);
    leanh::lean_closure_set(v___f_2925_, 2, v_a_2921_);
    leanh::lean_closure_set(v___f_2925_, 3, v_inst_2906_);
    leanh::lean_closure_set(v___f_2925_, 4, v_toBind_2907_);
    leanh::lean_closure_set(v___f_2925_, 5, v___f_2908_);
    leanh::lean_closure_set(v___f_2925_, 6, v___y_2924_);
    leanh::lean_closure_set(v___f_2925_, 7, v___x_2909_);
    leanh::lean_closure_set(v___f_2925_, 8, v___x_2910_);
    leanh::lean_closure_set(v___f_2925_, 9, v___x_2911_);
    leanh::lean_closure_set(v___f_2925_, 10, v___x_2912_);
    v___x_2926_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2904_, v_inst_2913_);
    v___x_2927_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_2927_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2927_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2927_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2927_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2927_, 4, v_inst_2914_);
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
    v___x_2929_ = leanh::lean_apply_1(v___x_6942__overap_2928_, v___y_2924_);
    v___x_2930_ = leanh::lean_apply_4(
        v_toBind_2907_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2929_,
        v___f_2925_,
    );
    return v___x_2930_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2931_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_2932_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_2933_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toBind_2934_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_2935_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2936_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2937_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2938_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2939_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2940_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_2941_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2942_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2943_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2944_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_2945_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_2946_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_2947_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_2948_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_x_2949_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2950_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_2951_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_res_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2951_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(
    mut v_toPure_2953_: *mut leanh::LeanObject,
    mut v___x_2954_: *mut leanh::LeanObject,
    mut v_inst_2955_: *mut leanh::LeanObject,
    mut v_inst_2956_: *mut leanh::LeanObject,
    mut v_toBind_2957_: *mut leanh::LeanObject,
    mut v___x_2958_: *mut leanh::LeanObject,
    mut v___x_2959_: *mut leanh::LeanObject,
    mut v___x_2960_: *mut leanh::LeanObject,
    mut v_inst_2961_: *mut leanh::LeanObject,
    mut v_inst_2962_: *mut leanh::LeanObject,
    mut v___x_2963_: *mut leanh::LeanObject,
    mut v___x_2964_: *mut leanh::LeanObject,
    mut v___x_2965_: *mut leanh::LeanObject,
    mut v___f_2966_: *mut leanh::LeanObject,
    mut v___x_2967_: *mut leanh::LeanObject,
    mut v_ids_2968_: *mut leanh::LeanObject,
    mut v_ref_2969_: *mut leanh::LeanObject,
    mut v___f_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2975_: usize = 0;
    let mut v___x_2976_: usize = 0;
    let mut v___x_6962__overap_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = leanh::lean_box(0);
    v___f_2973_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2973_, 0, v___x_2972_);
    leanh::lean_closure_set(v___f_2973_, 1, v_toPure_2953_);
    leanh::lean_inc_ref(v___x_2958_);
    leanh::lean_inc(v_toBind_2957_);
    v___f_2974_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    leanh::lean_closure_set(v___f_2974_, 0, v___x_2954_);
    leanh::lean_closure_set(v___f_2974_, 1, v_inst_2955_);
    leanh::lean_closure_set(v___f_2974_, 2, v_inst_2956_);
    leanh::lean_closure_set(v___f_2974_, 3, v_toBind_2957_);
    leanh::lean_closure_set(v___f_2974_, 4, v___f_2973_);
    leanh::lean_closure_set(v___f_2974_, 5, v___x_2972_);
    leanh::lean_closure_set(v___f_2974_, 6, v___x_2958_);
    leanh::lean_closure_set(v___f_2974_, 7, v___x_2959_);
    leanh::lean_closure_set(v___f_2974_, 8, v___x_2960_);
    leanh::lean_closure_set(v___f_2974_, 9, v_inst_2961_);
    leanh::lean_closure_set(v___f_2974_, 10, v_inst_2962_);
    leanh::lean_closure_set(v___f_2974_, 11, v___x_2963_);
    leanh::lean_closure_set(v___f_2974_, 12, v___x_2964_);
    leanh::lean_closure_set(v___f_2974_, 13, v___x_2965_);
    leanh::lean_closure_set(v___f_2974_, 14, v___f_2966_);
    leanh::lean_closure_set(v___f_2974_, 15, v___x_2967_);
    leanh::lean_closure_set(v___f_2974_, 16, v_a_2971_);
    v_sz_2975_ = lean_array_size(v_ids_2968_);
    v___x_2976_ = 0usize;
    v___x_6962__overap_2977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2958_,
        v_ids_2968_,
        v___f_2974_,
        v_sz_2975_,
        v___x_2976_,
        v___x_2972_,
    );
    v___x_2978_ = leanh::lean_apply_1(v___x_6962__overap_2977_, v_ref_2969_);
    v___x_2979_ = leanh::lean_apply_4(
        v_toBind_2957_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2978_,
        v___f_2970_,
    );
    return v___x_2979_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_2980_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_2981_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_2982_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_2983_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_toBind_2984_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2985_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2986_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2987_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_2988_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2989_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_2990_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2991_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2992_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_2993_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2994_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_ids_2995_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_ref_2996_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_2997_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_2998_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3000_: *mut leanh::LeanObject,
    mut v___x_3001_: *mut leanh::LeanObject,
    mut v___x_3002_: *mut leanh::LeanObject,
    mut v___x_3003_: *mut leanh::LeanObject,
    mut v_toBind_3004_: *mut leanh::LeanObject,
    mut v___f_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_x_3007_: *mut leanh::LeanObject,
    mut v___y_3008_: *mut leanh::LeanObject,
    mut v___y_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982__overap_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3010_ = leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3010_, 0, v_inst_3000_);
    leanh::lean_closure_set(v___f_3010_, 1, v___x_3001_);
    v___x_6982__overap_3011_ =
        l_Lean_activateScoped___redArg(v___x_3002_, v___x_3003_, v___f_3010_, v_a_3006_);
    leanh::lean_inc(v___y_3009_);
    v___x_3012_ = leanh::lean_apply_1(v___x_6982__overap_3011_, v___y_3009_);
    v___x_3013_ = leanh::lean_apply_4(
        v_toBind_3004_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3012_,
        v___f_3005_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(
    mut v_inst_3014_: *mut leanh::LeanObject,
    mut v___x_3015_: *mut leanh::LeanObject,
    mut v___x_3016_: *mut leanh::LeanObject,
    mut v___x_3017_: *mut leanh::LeanObject,
    mut v_toBind_3018_: *mut leanh::LeanObject,
    mut v___f_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_x_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3023_);
    return v_res_3024_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
    mut v___x_3025_: *mut leanh::LeanObject,
    mut v___f_3026_: *mut leanh::LeanObject,
    mut v___x_3027_: *mut leanh::LeanObject,
    mut v___y_3028_: *mut leanh::LeanObject,
    mut v_toBind_3029_: *mut leanh::LeanObject,
    mut v___f_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6989__overap_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6989__overap_3032_ =
        l_List_forIn_x27_loop___redArg(v___x_3025_, v___f_3026_, v_a_3031_, v___x_3027_);
    leanh::lean_inc(v___y_3028_);
    v___x_3033_ = leanh::lean_apply_1(v___x_6989__overap_3032_, v___y_3028_);
    v___x_3034_ = leanh::lean_apply_4(
        v_toBind_3029_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3033_,
        v___f_3030_,
    );
    return v___x_3034_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(
    mut v___x_3035_: *mut leanh::LeanObject,
    mut v___f_3036_: *mut leanh::LeanObject,
    mut v___x_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v_toBind_3039_: *mut leanh::LeanObject,
    mut v___f_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
        v___x_3035_,
        v___f_3036_,
        v___x_3037_,
        v___y_3038_,
        v_toBind_3039_,
        v___f_3040_,
        v_a_3041_,
    );
    leanh::lean_dec(v_a_3041_);
    leanh::lean_dec(v___y_3038_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(
    mut v_inst_3045_: *mut leanh::LeanObject,
    mut v_inst_3046_: *mut leanh::LeanObject,
    mut v_inst_3047_: *mut leanh::LeanObject,
    mut v___x_3048_: *mut leanh::LeanObject,
    mut v_toBind_3049_: *mut leanh::LeanObject,
    mut v___f_3050_: *mut leanh::LeanObject,
    mut v___x_3051_: *mut leanh::LeanObject,
    mut v___f_3052_: *mut leanh::LeanObject,
    mut v_inst_3053_: *mut leanh::LeanObject,
    mut v_inst_3054_: *mut leanh::LeanObject,
    mut v_inst_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_x_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019__overap_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_inst_3046_);
                v___x_3060_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3045_, v_inst_3046_);
                v_getEnv_3061_ = leanh::lean_ctor_get(v_inst_3047_, 0);
                v_modifyEnv_3062_ = leanh::lean_ctor_get(v_inst_3047_, 1);
                v_isSharedCheck_3085_ = (!leanh::lean_is_exclusive(v_inst_3047_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_3064_ = v_inst_3047_;
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyEnv_3062_);
                    leanh::lean_inc(v_getEnv_3061_);
                    leanh::lean_dec(v_inst_3047_);
                    v___x_3064_ = leanh::lean_box(0);
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3066_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3067_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3067_, 0, v_modifyEnv_3062_);
                leanh::lean_closure_set(v___f_3067_, 1, v___x_3066_);
                v___x_3068_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3068_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3068_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3068_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3068_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3068_, 4, v_getEnv_3061_);
                if v_isShared_3065_ == 0 {
                    leanh::lean_ctor_set(v___x_3064_, 1, v___f_3067_);
                    leanh::lean_ctor_set(v___x_3064_, 0, v___x_3068_);
                    v___x_3070_ = v___x_3064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___f_3067_);
                    v___x_3070_ = v_reuseFailAlloc_3084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_toBind_3049_, 2);
                leanh::lean_inc_ref(v___x_3070_);
                leanh::lean_inc_ref_n(v___x_3048_, 3);
                v___f_3071_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed
                        as *mut core::ffi::c_void,
                    10,
                    6,
                );
                leanh::lean_closure_set(v___f_3071_, 0, v_inst_3046_);
                leanh::lean_closure_set(v___f_3071_, 1, v___x_3066_);
                leanh::lean_closure_set(v___f_3071_, 2, v___x_3048_);
                leanh::lean_closure_set(v___f_3071_, 3, v___x_3070_);
                leanh::lean_closure_set(v___f_3071_, 4, v_toBind_3049_);
                leanh::lean_closure_set(v___f_3071_, 5, v___f_3050_);
                leanh::lean_inc_n(v___y_3059_, 2);
                v___f_3072_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_3072_, 0, v___x_3048_);
                leanh::lean_closure_set(v___f_3072_, 1, v___f_3071_);
                leanh::lean_closure_set(v___f_3072_, 2, v___x_3051_);
                leanh::lean_closure_set(v___f_3072_, 3, v___y_3059_);
                leanh::lean_closure_set(v___f_3072_, 4, v_toBind_3049_);
                leanh::lean_closure_set(v___f_3072_, 5, v___f_3052_);
                leanh::lean_inc_ref(v_inst_3053_);
                v___f_3073_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3073_, 0, v_inst_3053_);
                v___f_3074_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3074_, 0, v_inst_3053_);
                v___x_3075_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3075_, 0, v___f_3073_);
                leanh::lean_ctor_set(v___x_3075_, 1, v___f_3074_);
                v___x_3076_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3077_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3066_,
                    v___x_3076_,
                    v_inst_3054_,
                );
                v___f_3078_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3078_, 0, v_inst_3055_);
                leanh::lean_closure_set(v___f_3078_, 1, v___x_3066_);
                v___x_3079_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3078_,
                    v___x_3048_,
                );
                v___x_3080_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3080_, 0, v___x_3075_);
                leanh::lean_ctor_set(v___x_3080_, 1, v___x_3077_);
                leanh::lean_ctor_set(v___x_3080_, 2, v___x_3079_);
                v___x_7019__overap_3081_ = l_Lean_resolveNamespace___redArg(
                    v___x_3048_,
                    v___x_3060_,
                    v___x_3070_,
                    v___x_3080_,
                    v_a_3056_,
                );
                v___x_3082_ = leanh::lean_apply_1(v___x_7019__overap_3081_, v___y_3059_);
                v___x_3083_ = leanh::lean_apply_4(
                    v_toBind_3049_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_inst_3086_: *mut leanh::LeanObject,
    mut v_inst_3087_: *mut leanh::LeanObject,
    mut v_inst_3088_: *mut leanh::LeanObject,
    mut v___x_3089_: *mut leanh::LeanObject,
    mut v_toBind_3090_: *mut leanh::LeanObject,
    mut v___f_3091_: *mut leanh::LeanObject,
    mut v___x_3092_: *mut leanh::LeanObject,
    mut v___f_3093_: *mut leanh::LeanObject,
    mut v_inst_3094_: *mut leanh::LeanObject,
    mut v_inst_3095_: *mut leanh::LeanObject,
    mut v_inst_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
    mut v_x_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3100_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(
    mut v_inst_3102_: *mut leanh::LeanObject,
    mut v___x_3103_: *mut leanh::LeanObject,
    mut v___x_3104_: *mut leanh::LeanObject,
    mut v___x_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v_toBind_3108_: *mut leanh::LeanObject,
    mut v___f_3109_: *mut leanh::LeanObject,
    mut v_a_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037__overap_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3111_ = leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3111_, 0, v_inst_3102_);
    leanh::lean_closure_set(v___f_3111_, 1, v___x_3103_);
    v___x_7037__overap_3112_ =
        l_Lean_activateScoped___redArg(v___x_3104_, v___x_3105_, v___f_3111_, v_a_3106_);
    leanh::lean_inc(v___y_3107_);
    v___x_3113_ = leanh::lean_apply_1(v___x_7037__overap_3112_, v___y_3107_);
    v___x_3114_ = leanh::lean_apply_4(
        v_toBind_3108_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3113_,
        v___f_3109_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(
    mut v_inst_3115_: *mut leanh::LeanObject,
    mut v___x_3116_: *mut leanh::LeanObject,
    mut v___x_3117_: *mut leanh::LeanObject,
    mut v___x_3118_: *mut leanh::LeanObject,
    mut v_a_3119_: *mut leanh::LeanObject,
    mut v___y_3120_: *mut leanh::LeanObject,
    mut v_toBind_3121_: *mut leanh::LeanObject,
    mut v___f_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3120_);
    return v_res_3124_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(
    mut v_inst_3125_: *mut leanh::LeanObject,
    mut v___x_3126_: *mut leanh::LeanObject,
    mut v___x_3127_: *mut leanh::LeanObject,
    mut v___x_3128_: *mut leanh::LeanObject,
    mut v_toBind_3129_: *mut leanh::LeanObject,
    mut v___f_3130_: *mut leanh::LeanObject,
    mut v___x_3131_: *mut leanh::LeanObject,
    mut v_a_3132_: *mut leanh::LeanObject,
    mut v_x_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_3129_);
    leanh::lean_inc(v___y_3135_);
    leanh::lean_inc(v_a_3132_);
    leanh::lean_inc(v_inst_3125_);
    v___f_3136_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_3136_, 0, v_inst_3125_);
    leanh::lean_closure_set(v___f_3136_, 1, v___x_3126_);
    leanh::lean_closure_set(v___f_3136_, 2, v___x_3127_);
    leanh::lean_closure_set(v___f_3136_, 3, v___x_3128_);
    leanh::lean_closure_set(v___f_3136_, 4, v_a_3132_);
    leanh::lean_closure_set(v___f_3136_, 5, v___y_3135_);
    leanh::lean_closure_set(v___f_3136_, 6, v_toBind_3129_);
    leanh::lean_closure_set(v___f_3136_, 7, v___f_3130_);
    v___x_3137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3137_, 0, v_a_3132_);
    leanh::lean_ctor_set(v___x_3137_, 1, v___x_3131_);
    v___x_3138_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_3125_,
        v___x_3137_,
        v___y_3135_,
    );
    v___x_3139_ = leanh::lean_apply_4(
        v_toBind_3129_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3138_,
        v___f_3136_,
    );
    return v___x_3139_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(
    mut v_inst_3140_: *mut leanh::LeanObject,
    mut v___x_3141_: *mut leanh::LeanObject,
    mut v___x_3142_: *mut leanh::LeanObject,
    mut v___x_3143_: *mut leanh::LeanObject,
    mut v_toBind_3144_: *mut leanh::LeanObject,
    mut v___f_3145_: *mut leanh::LeanObject,
    mut v___x_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
    mut v_x_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3150_);
    return v_res_3151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(
    mut v_inst_3152_: *mut leanh::LeanObject,
    mut v_inst_3153_: *mut leanh::LeanObject,
    mut v_inst_3154_: *mut leanh::LeanObject,
    mut v___x_3155_: *mut leanh::LeanObject,
    mut v_toBind_3156_: *mut leanh::LeanObject,
    mut v___f_3157_: *mut leanh::LeanObject,
    mut v___x_3158_: *mut leanh::LeanObject,
    mut v___x_3159_: *mut leanh::LeanObject,
    mut v___f_3160_: *mut leanh::LeanObject,
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
    mut v_inst_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_x_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088__overap_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_inst_3153_);
                v___x_3168_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3152_, v_inst_3153_);
                v_getEnv_3169_ = leanh::lean_ctor_get(v_inst_3154_, 0);
                v_modifyEnv_3170_ = leanh::lean_ctor_get(v_inst_3154_, 1);
                v_isSharedCheck_3193_ = (!leanh::lean_is_exclusive(v_inst_3154_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v___x_3172_ = v_inst_3154_;
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyEnv_3170_);
                    leanh::lean_inc(v_getEnv_3169_);
                    leanh::lean_dec(v_inst_3154_);
                    v___x_3172_ = leanh::lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3175_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3175_, 0, v_modifyEnv_3170_);
                leanh::lean_closure_set(v___f_3175_, 1, v___x_3174_);
                v___x_3176_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3176_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3176_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3176_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3176_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3176_, 4, v_getEnv_3169_);
                if v_isShared_3173_ == 0 {
                    leanh::lean_ctor_set(v___x_3172_, 1, v___f_3175_);
                    leanh::lean_ctor_set(v___x_3172_, 0, v___x_3176_);
                    v___x_3178_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___f_3175_);
                    v___x_3178_ = v_reuseFailAlloc_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_toBind_3156_, 2);
                leanh::lean_inc_ref(v___x_3178_);
                leanh::lean_inc_ref_n(v___x_3155_, 3);
                v___f_3179_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_3179_, 0, v_inst_3153_);
                leanh::lean_closure_set(v___f_3179_, 1, v___x_3174_);
                leanh::lean_closure_set(v___f_3179_, 2, v___x_3155_);
                leanh::lean_closure_set(v___f_3179_, 3, v___x_3178_);
                leanh::lean_closure_set(v___f_3179_, 4, v_toBind_3156_);
                leanh::lean_closure_set(v___f_3179_, 5, v___f_3157_);
                leanh::lean_closure_set(v___f_3179_, 6, v___x_3158_);
                leanh::lean_inc_n(v___y_3167_, 2);
                v___f_3180_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_3180_, 0, v___x_3155_);
                leanh::lean_closure_set(v___f_3180_, 1, v___f_3179_);
                leanh::lean_closure_set(v___f_3180_, 2, v___x_3159_);
                leanh::lean_closure_set(v___f_3180_, 3, v___y_3167_);
                leanh::lean_closure_set(v___f_3180_, 4, v_toBind_3156_);
                leanh::lean_closure_set(v___f_3180_, 5, v___f_3160_);
                leanh::lean_inc_ref(v_inst_3161_);
                v___f_3181_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3181_, 0, v_inst_3161_);
                v___f_3182_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3182_, 0, v_inst_3161_);
                v___x_3183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3183_, 0, v___f_3181_);
                leanh::lean_ctor_set(v___x_3183_, 1, v___f_3182_);
                v___x_3184_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3185_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3174_,
                    v___x_3184_,
                    v_inst_3162_,
                );
                v___f_3186_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3186_, 0, v_inst_3163_);
                leanh::lean_closure_set(v___f_3186_, 1, v___x_3174_);
                v___x_3187_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3186_,
                    v___x_3155_,
                );
                v___x_3188_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3188_, 0, v___x_3183_);
                leanh::lean_ctor_set(v___x_3188_, 1, v___x_3185_);
                leanh::lean_ctor_set(v___x_3188_, 2, v___x_3187_);
                v___x_7088__overap_3189_ = l_Lean_resolveNamespace___redArg(
                    v___x_3155_,
                    v___x_3168_,
                    v___x_3178_,
                    v___x_3188_,
                    v_a_3164_,
                );
                v___x_3190_ = leanh::lean_apply_1(v___x_7088__overap_3189_, v___y_3167_);
                v___x_3191_ = leanh::lean_apply_4(
                    v_toBind_3156_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_inst_3194_: *mut leanh::LeanObject,
    mut v_inst_3195_: *mut leanh::LeanObject,
    mut v_inst_3196_: *mut leanh::LeanObject,
    mut v___x_3197_: *mut leanh::LeanObject,
    mut v_toBind_3198_: *mut leanh::LeanObject,
    mut v___f_3199_: *mut leanh::LeanObject,
    mut v___x_3200_: *mut leanh::LeanObject,
    mut v___x_3201_: *mut leanh::LeanObject,
    mut v___f_3202_: *mut leanh::LeanObject,
    mut v_inst_3203_: *mut leanh::LeanObject,
    mut v_inst_3204_: *mut leanh::LeanObject,
    mut v_inst_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_x_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3209_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(
    mut v_toPure_3238_: *mut leanh::LeanObject,
    mut v_inst_3239_: *mut leanh::LeanObject,
    mut v_toBind_3240_: *mut leanh::LeanObject,
    mut v___x_3241_: u8,
    mut v___x_3242_: *mut leanh::LeanObject,
    mut v___x_3243_: *mut leanh::LeanObject,
    mut v___x_3244_: *mut leanh::LeanObject,
    mut v_stx_3245_: *mut leanh::LeanObject,
    mut v___f_3246_: *mut leanh::LeanObject,
    mut v_inst_3247_: *mut leanh::LeanObject,
    mut v_inst_3248_: *mut leanh::LeanObject,
    mut v_inst_3249_: *mut leanh::LeanObject,
    mut v___f_3250_: *mut leanh::LeanObject,
    mut v___f_3251_: *mut leanh::LeanObject,
    mut v_inst_3252_: *mut leanh::LeanObject,
    mut v_inst_3253_: *mut leanh::LeanObject,
    mut v___x_3254_: *mut leanh::LeanObject,
    mut v_inst_3255_: *mut leanh::LeanObject,
    mut v_inst_3256_: *mut leanh::LeanObject,
    mut v_inst_3257_: *mut leanh::LeanObject,
    mut v___f_3258_: *mut leanh::LeanObject,
    mut v_ref_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: u8 = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___f_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125__overap_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151__overap_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3303_: usize = 0;
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v_tos_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_froms_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179__overap_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___f_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223__overap_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___f_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244__overap_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v___f_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nss_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3423_: usize = 0;
    let mut v___x_3424_: usize = 0;
    let mut v___x_7255__overap_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nss_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3437_: usize = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_7267__overap_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_toBind_3240_);
                leanh::lean_inc(v_inst_3239_);
                leanh::lean_inc(v_ref_3259_);
                leanh::lean_inc(v_toPure_3238_);
                v___f_3260_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3260_, 0, v_toPure_3238_);
                leanh::lean_closure_set(v___f_3260_, 1, v_ref_3259_);
                leanh::lean_closure_set(v___f_3260_, 2, v_inst_3239_);
                leanh::lean_closure_set(v___f_3260_, 3, v_toBind_3240_);
                if v___x_3241_ == 0 {
                    v___x_3261_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0;
                    leanh::lean_inc_ref(v___x_3244_);
                    leanh::lean_inc_ref(v___x_3243_);
                    leanh::lean_inc_ref(v___x_3242_);
                    v___x_3262_ =
                        l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3261_);
                    leanh::lean_inc(v_stx_3245_);
                    v___x_3263_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3262_);
                    leanh::lean_dec(v___x_3262_);
                    if v___x_3263_ == 0 {
                        v___x_3264_ =
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1;
                        leanh::lean_inc_ref(v___x_3244_);
                        leanh::lean_inc_ref(v___x_3243_);
                        leanh::lean_inc_ref(v___x_3242_);
                        v___x_3265_ =
                            l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3264_);
                        leanh::lean_inc(v_stx_3245_);
                        v___x_3266_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3265_);
                        leanh::lean_dec(v___x_3265_);
                        if v___x_3266_ == 0 {
                            v___x_3267_ =
                                l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2;
                            leanh::lean_inc_ref(v___x_3244_);
                            leanh::lean_inc_ref(v___x_3243_);
                            leanh::lean_inc_ref(v___x_3242_);
                            v___x_3268_ = l_Lean_Name_mkStr4(
                                v___x_3242_,
                                v___x_3243_,
                                v___x_3244_,
                                v___x_3267_,
                            );
                            leanh::lean_inc(v_stx_3245_);
                            v___x_3269_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3268_);
                            leanh::lean_dec(v___x_3268_);
                            if v___x_3269_ == 0 {
                                leanh::lean_dec_ref(v___f_3258_);
                                v___x_3270_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3;
                                leanh::lean_inc_ref(v___x_3244_);
                                leanh::lean_inc_ref(v___x_3243_);
                                leanh::lean_inc_ref(v___x_3242_);
                                v___x_3271_ = l_Lean_Name_mkStr4(
                                    v___x_3242_,
                                    v___x_3243_,
                                    v___x_3244_,
                                    v___x_3270_,
                                );
                                leanh::lean_inc(v_stx_3245_);
                                v___x_3272_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3271_);
                                leanh::lean_dec(v___x_3271_);
                                if v___x_3272_ == 0 {
                                    leanh::lean_dec(v_inst_3257_);
                                    leanh::lean_dec_ref(v_inst_3256_);
                                    leanh::lean_dec_ref(v_inst_3255_);
                                    leanh::lean_dec_ref(v___x_3254_);
                                    leanh::lean_dec(v_inst_3253_);
                                    leanh::lean_dec_ref(v_inst_3252_);
                                    leanh::lean_dec_ref(v___f_3251_);
                                    leanh::lean_dec_ref(v___f_3250_);
                                    leanh::lean_dec_ref(v_inst_3249_);
                                    leanh::lean_dec_ref(v_inst_3248_);
                                    leanh::lean_dec(v_stx_3245_);
                                    leanh::lean_dec_ref(v___x_3244_);
                                    leanh::lean_dec_ref(v___x_3243_);
                                    leanh::lean_dec_ref(v___x_3242_);
                                    leanh::lean_dec(v_inst_3239_);
                                    leanh::lean_dec(v_toPure_3238_);
                                    leanh::lean_inc(v_ref_3259_);
                                    v___f_3273_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_3273_, 0, v___f_3246_);
                                    leanh::lean_closure_set(v___f_3273_, 1, v_ref_3259_);
                                    leanh::lean_inc_ref(v_inst_3247_);
                                    v___f_3274_ = leanh::lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        1,
                                    );
                                    leanh::lean_closure_set(v___f_3274_, 0, v_inst_3247_);
                                    v___f_3275_ = leanh::lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                                            as *mut core::ffi::c_void,
                                        5,
                                        1,
                                    );
                                    leanh::lean_closure_set(v___f_3275_, 0, v_inst_3247_);
                                    v___x_3276_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3276_, 0, v___f_3274_);
                                    leanh::lean_ctor_set(v___x_3276_, 1, v___f_3275_);
                                    v___x_7125__overap_3277_ =
                                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3276_);
                                    v___x_3278_ = leanh::lean_apply_1(
                                        v___x_7125__overap_3277_,
                                        v_ref_3259_,
                                    );
                                    leanh::lean_inc(v_toBind_3240_);
                                    v___x_3279_ = leanh::lean_apply_4(
                                        v_toBind_3240_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_3278_,
                                        v___f_3273_,
                                    );
                                    v___x_3280_ = leanh::lean_apply_4(
                                        v_toBind_3240_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_3279_,
                                        v___f_3260_,
                                    );
                                    return v___x_3280_;
                                } else {
                                    leanh::lean_inc_n(v_ref_3259_, 2);
                                    leanh::lean_inc(v___f_3246_);
                                    v___f_3281_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_3281_, 0, v___f_3246_);
                                    leanh::lean_closure_set(v___f_3281_, 1, v_ref_3259_);
                                    v___f_3282_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_3282_, 0, v___f_3246_);
                                    leanh::lean_closure_set(v___f_3282_, 1, v_ref_3259_);
                                    v___x_3283_ = leanh::lean_unsigned_to_nat(0);
                                    v_ns_3284_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3283_);
                                    v___x_3285_ = leanh::lean_unsigned_to_nat(2);
                                    v___f_3286_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    leanh::lean_closure_set(v___f_3286_, 0, v___x_3242_);
                                    leanh::lean_closure_set(v___f_3286_, 1, v___x_3243_);
                                    leanh::lean_closure_set(v___f_3286_, 2, v___x_3244_);
                                    leanh::lean_closure_set(v___f_3286_, 3, v___x_3283_);
                                    leanh::lean_closure_set(v___f_3286_, 4, v___x_3285_);
                                    v___x_3287_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3285_);
                                    leanh::lean_dec(v_stx_3245_);
                                    v___x_3288_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13;
                                    v___x_3333_ = l_Lean_Syntax_getArgs(v___x_3287_);
                                    leanh::lean_dec(v___x_3287_);
                                    v___x_3334_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14;
                                    v___x_3335_ = lean_array_get_size(v___x_3333_);
                                    v___x_3336_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                                    v___x_3337_ = lean_nat_dec_lt(v___x_3283_, v___x_3335_);
                                    if v___x_3337_ == 0 {
                                        leanh::lean_dec_ref(v___x_3333_);
                                        v___y_3290_ = v___x_3334_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3338_ =
                                            leanh::lean_box((v___x_3272_) as usize);
                                        v___x_3339_ =
                                            leanh::lean_box((v___x_3269_) as usize);
                                        v___f_3340_ = leanh::lean_alloc_closure(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed as *mut core::ffi::c_void, 4, 2);
                                        leanh::lean_closure_set(v___f_3340_, 0, v___x_3338_);
                                        leanh::lean_closure_set(v___f_3340_, 1, v___x_3339_);
                                        v___x_3341_ =
                                            leanh::lean_box((v___x_3272_) as usize);
                                        v___x_3342_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
                                        leanh::lean_ctor_set(v___x_3342_, 1, v___x_3334_);
                                        v___x_3343_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
                                        if v___x_3343_ == 0 {
                                            if v___x_3337_ == 0 {
                                                leanh::lean_dec_ref_known(v___x_3342_, 2);
                                                leanh::lean_dec_ref(v___f_3340_);
                                                leanh::lean_dec_ref(v___x_3333_);
                                                v___y_3290_ = v___x_3334_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3344_ = 0usize;
                                                v___x_3345_ = lean_usize_of_nat(v___x_3335_);
                                                v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3344_, v___x_3345_, v___x_3342_);
                                                v_snd_3347_ =
                                                    leanh::lean_ctor_get(v___x_3346_, 1);
                                                leanh::lean_inc(v_snd_3347_);
                                                leanh::lean_dec(v___x_3346_);
                                                v___y_3290_ = v_snd_3347_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___x_3348_ = 0usize;
                                            v___x_3349_ = lean_usize_of_nat(v___x_3335_);
                                            v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3348_, v___x_3349_, v___x_3342_);
                                            v_snd_3351_ =
                                                leanh::lean_ctor_get(v___x_3350_, 1);
                                            leanh::lean_inc(v_snd_3351_);
                                            leanh::lean_dec(v___x_3350_);
                                            v___y_3290_ = v_snd_3351_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___f_3251_);
                                leanh::lean_dec_ref(v___f_3250_);
                                leanh::lean_dec_ref(v___x_3244_);
                                leanh::lean_dec_ref(v___x_3243_);
                                leanh::lean_dec_ref(v___x_3242_);
                                leanh::lean_inc(v_inst_3239_);
                                v___x_3352_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                    v_inst_3248_,
                                    v_inst_3239_,
                                );
                                v_getEnv_3353_ = leanh::lean_ctor_get(v_inst_3249_, 0);
                                v_modifyEnv_3354_ = leanh::lean_ctor_get(v_inst_3249_, 1);
                                v_isSharedCheck_3383_ =
                                    (!leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                                if v_isSharedCheck_3383_ == 0 {
                                    v___x_3356_ = v_inst_3249_;
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_modifyEnv_3354_);
                                    leanh::lean_inc(v_getEnv_3353_);
                                    leanh::lean_dec(v_inst_3249_);
                                    v___x_3356_ = leanh::lean_box(0);
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___f_3258_);
                            leanh::lean_dec_ref(v___f_3251_);
                            leanh::lean_dec_ref(v___f_3250_);
                            leanh::lean_dec_ref(v___x_3244_);
                            leanh::lean_dec_ref(v___x_3243_);
                            leanh::lean_dec_ref(v___x_3242_);
                            leanh::lean_inc(v_inst_3239_);
                            v___x_3384_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                v_inst_3248_,
                                v_inst_3239_,
                            );
                            v_getEnv_3385_ = leanh::lean_ctor_get(v_inst_3249_, 0);
                            v_modifyEnv_3386_ = leanh::lean_ctor_get(v_inst_3249_, 1);
                            v_isSharedCheck_3415_ =
                                (!leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                            if v_isSharedCheck_3415_ == 0 {
                                v___x_3388_ = v_inst_3249_;
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_modifyEnv_3386_);
                                leanh::lean_inc(v_getEnv_3385_);
                                leanh::lean_dec(v_inst_3249_);
                                v___x_3388_ = leanh::lean_box(0);
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_3258_);
                        leanh::lean_dec(v_inst_3257_);
                        leanh::lean_dec_ref(v_inst_3256_);
                        leanh::lean_dec_ref(v_inst_3255_);
                        leanh::lean_dec_ref(v___f_3251_);
                        leanh::lean_dec_ref(v___f_3250_);
                        leanh::lean_dec_ref(v___x_3244_);
                        leanh::lean_dec_ref(v___x_3243_);
                        leanh::lean_dec_ref(v___x_3242_);
                        leanh::lean_inc(v_ref_3259_);
                        v___f_3416_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_3416_, 0, v___f_3246_);
                        leanh::lean_closure_set(v___f_3416_, 1, v_ref_3259_);
                        v___x_3417_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3418_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3417_);
                        leanh::lean_dec(v_stx_3245_);
                        v_nss_3419_ = l_Lean_Syntax_getArgs(v___x_3418_);
                        leanh::lean_dec(v___x_3418_);
                        v___x_3420_ = leanh::lean_box(0);
                        v___f_3421_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_3421_, 0, v___x_3420_);
                        leanh::lean_closure_set(v___f_3421_, 1, v_toPure_3238_);
                        leanh::lean_inc_ref(v___f_3421_);
                        leanh::lean_inc_n(v_toBind_3240_, 2);
                        leanh::lean_inc_ref(v___x_3254_);
                        v___f_3422_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed
                                as *mut core::ffi::c_void,
                            15,
                            11,
                        );
                        leanh::lean_closure_set(v___f_3422_, 0, v_inst_3248_);
                        leanh::lean_closure_set(v___f_3422_, 1, v_inst_3239_);
                        leanh::lean_closure_set(v___f_3422_, 2, v_inst_3249_);
                        leanh::lean_closure_set(v___f_3422_, 3, v___x_3254_);
                        leanh::lean_closure_set(v___f_3422_, 4, v_toBind_3240_);
                        leanh::lean_closure_set(v___f_3422_, 5, v___f_3421_);
                        leanh::lean_closure_set(v___f_3422_, 6, v___x_3420_);
                        leanh::lean_closure_set(v___f_3422_, 7, v___f_3421_);
                        leanh::lean_closure_set(v___f_3422_, 8, v_inst_3247_);
                        leanh::lean_closure_set(v___f_3422_, 9, v_inst_3252_);
                        leanh::lean_closure_set(v___f_3422_, 10, v_inst_3253_);
                        v_sz_3423_ = lean_array_size(v_nss_3419_);
                        v___x_3424_ = 0usize;
                        v___x_7255__overap_3425_ =
                            l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_3254_,
                                v_nss_3419_,
                                v___f_3422_,
                                v_sz_3423_,
                                v___x_3424_,
                                v___x_3420_,
                            );
                        v___x_3426_ =
                            leanh::lean_apply_1(v___x_7255__overap_3425_, v_ref_3259_);
                        v___x_3427_ = leanh::lean_apply_4(
                            v_toBind_3240_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3426_,
                            v___f_3416_,
                        );
                        v___x_3428_ = leanh::lean_apply_4(
                            v_toBind_3240_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3427_,
                            v___f_3260_,
                        );
                        return v___x_3428_;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_3258_);
                    leanh::lean_dec(v_inst_3257_);
                    leanh::lean_dec_ref(v_inst_3256_);
                    leanh::lean_dec_ref(v_inst_3255_);
                    leanh::lean_dec_ref(v___f_3251_);
                    leanh::lean_dec_ref(v___f_3250_);
                    leanh::lean_dec_ref(v___x_3244_);
                    leanh::lean_dec_ref(v___x_3243_);
                    leanh::lean_dec_ref(v___x_3242_);
                    leanh::lean_inc(v_ref_3259_);
                    v___f_3429_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3429_, 0, v___f_3246_);
                    leanh::lean_closure_set(v___f_3429_, 1, v_ref_3259_);
                    v___x_3430_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3431_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3430_);
                    leanh::lean_dec(v_stx_3245_);
                    v___x_3432_ = leanh::lean_box(0);
                    v_nss_3433_ = l_Lean_Syntax_getArgs(v___x_3431_);
                    leanh::lean_dec(v___x_3431_);
                    v___x_3434_ = leanh::lean_box(0);
                    v___f_3435_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3435_, 0, v___x_3434_);
                    leanh::lean_closure_set(v___f_3435_, 1, v_toPure_3238_);
                    leanh::lean_inc_ref(v___f_3435_);
                    leanh::lean_inc_n(v_toBind_3240_, 2);
                    leanh::lean_inc_ref(v___x_3254_);
                    v___f_3436_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed
                            as *mut core::ffi::c_void,
                        16,
                        12,
                    );
                    leanh::lean_closure_set(v___f_3436_, 0, v_inst_3248_);
                    leanh::lean_closure_set(v___f_3436_, 1, v_inst_3239_);
                    leanh::lean_closure_set(v___f_3436_, 2, v_inst_3249_);
                    leanh::lean_closure_set(v___f_3436_, 3, v___x_3254_);
                    leanh::lean_closure_set(v___f_3436_, 4, v_toBind_3240_);
                    leanh::lean_closure_set(v___f_3436_, 5, v___f_3435_);
                    leanh::lean_closure_set(v___f_3436_, 6, v___x_3432_);
                    leanh::lean_closure_set(v___f_3436_, 7, v___x_3434_);
                    leanh::lean_closure_set(v___f_3436_, 8, v___f_3435_);
                    leanh::lean_closure_set(v___f_3436_, 9, v_inst_3247_);
                    leanh::lean_closure_set(v___f_3436_, 10, v_inst_3252_);
                    leanh::lean_closure_set(v___f_3436_, 11, v_inst_3253_);
                    v_sz_3437_ = lean_array_size(v_nss_3433_);
                    v___x_3438_ = 0usize;
                    v___x_7267__overap_3439_ =
                        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3254_,
                            v_nss_3433_,
                            v___f_3436_,
                            v_sz_3437_,
                            v___x_3438_,
                            v___x_3434_,
                        );
                    v___x_3440_ = leanh::lean_apply_1(v___x_7267__overap_3439_, v_ref_3259_);
                    v___x_3441_ = leanh::lean_apply_4(
                        v_toBind_3240_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3440_,
                        v___f_3429_,
                    );
                    v___x_3442_ = leanh::lean_apply_4(
                        v_toBind_3240_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
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
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3288_,
                    v___f_3286_,
                    v_sz_3291_,
                    v___x_3292_,
                    v___y_3290_,
                );
                if leanh::lean_obj_tag(v___x_3293_) == 0 {
                    leanh::lean_dec(v_ns_3284_);
                    leanh::lean_dec_ref(v___f_3281_);
                    leanh::lean_dec(v_inst_3257_);
                    leanh::lean_dec_ref(v_inst_3256_);
                    leanh::lean_dec_ref(v_inst_3255_);
                    leanh::lean_dec_ref(v___x_3254_);
                    leanh::lean_dec(v_inst_3253_);
                    leanh::lean_dec_ref(v_inst_3252_);
                    leanh::lean_dec_ref(v___f_3251_);
                    leanh::lean_dec_ref(v___f_3250_);
                    leanh::lean_dec_ref(v_inst_3249_);
                    leanh::lean_dec_ref(v_inst_3248_);
                    leanh::lean_dec(v_inst_3239_);
                    leanh::lean_dec(v_toPure_3238_);
                    leanh::lean_inc_ref(v_inst_3247_);
                    v___f_3294_ = leanh::lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    leanh::lean_closure_set(v___f_3294_, 0, v_inst_3247_);
                    v___f_3295_ = leanh::lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    leanh::lean_closure_set(v___f_3295_, 0, v_inst_3247_);
                    v___x_3296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3296_, 0, v___f_3294_);
                    leanh::lean_ctor_set(v___x_3296_, 1, v___f_3295_);
                    v___x_7151__overap_3297_ =
                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3296_);
                    v___x_3298_ = leanh::lean_apply_1(v___x_7151__overap_3297_, v_ref_3259_);
                    leanh::lean_inc(v_toBind_3240_);
                    v___x_3299_ = leanh::lean_apply_4(
                        v_toBind_3240_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3298_,
                        v___f_3282_,
                    );
                    v___x_3300_ = leanh::lean_apply_4(
                        v_toBind_3240_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3299_,
                        v___f_3260_,
                    );
                    return v___x_3300_;
                } else {
                    leanh::lean_dec_ref(v___f_3282_);
                    v_val_3301_ = leanh::lean_ctor_get(v___x_3293_, 0);
                    leanh::lean_inc(v_val_3301_);
                    leanh::lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3302_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_sz_3303_ = lean_array_size(v_val_3301_);
                    leanh::lean_inc(v_inst_3239_);
                    v___x_3304_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                        v_inst_3248_,
                        v_inst_3239_,
                    );
                    v_getEnv_3305_ = leanh::lean_ctor_get(v_inst_3249_, 0);
                    v_modifyEnv_3306_ = leanh::lean_ctor_get(v_inst_3249_, 1);
                    v_isSharedCheck_3332_ = (!leanh::lean_is_exclusive(v_inst_3249_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3308_ = v_inst_3249_;
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_modifyEnv_3306_);
                        leanh::lean_inc(v_getEnv_3305_);
                        leanh::lean_dec(v_inst_3249_);
                        v___x_3308_ = leanh::lean_box(0);
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_3301_);
                v_tos_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3302_,
                    v___f_3250_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v_froms_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3302_,
                    v___f_3251_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v___x_3312_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3313_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3313_, 0, v_modifyEnv_3306_);
                leanh::lean_closure_set(v___f_3313_, 1, v___x_3312_);
                v___x_3314_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3314_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3314_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3314_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3314_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3314_, 4, v_getEnv_3305_);
                if v_isShared_3309_ == 0 {
                    leanh::lean_ctor_set(v___x_3308_, 1, v___f_3313_);
                    leanh::lean_ctor_set(v___x_3308_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3308_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___f_3313_);
                    v___x_3316_ = v_reuseFailAlloc_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_inst_3247_);
                v___f_3317_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3317_, 0, v_inst_3247_);
                v___f_3318_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3318_, 0, v_inst_3247_);
                v___x_3319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3319_, 0, v___f_3317_);
                leanh::lean_ctor_set(v___x_3319_, 1, v___f_3318_);
                v___x_3320_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3321_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3312_,
                    v___x_3320_,
                    v_inst_3252_,
                );
                v___f_3322_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3322_, 0, v_inst_3253_);
                leanh::lean_closure_set(v___f_3322_, 1, v___x_3312_);
                leanh::lean_inc_ref_n(v___x_3254_, 2);
                leanh::lean_inc_ref(v___f_3322_);
                v___x_3323_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3322_,
                    v___x_3254_,
                );
                leanh::lean_inc(v___x_3323_);
                leanh::lean_inc_ref(v___x_3321_);
                leanh::lean_inc_ref(v___x_3319_);
                v___x_3324_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3324_, 0, v___x_3319_);
                leanh::lean_ctor_set(v___x_3324_, 1, v___x_3321_);
                leanh::lean_ctor_set(v___x_3324_, 2, v___x_3323_);
                v___x_3325_ =
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1;
                leanh::lean_inc(v_ref_3259_);
                leanh::lean_inc_ref(v___x_3304_);
                leanh::lean_inc_ref(v___x_3324_);
                leanh::lean_inc_ref(v___x_3316_);
                leanh::lean_inc_n(v_toBind_3240_, 2);
                v___f_3326_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed
                        as *mut core::ffi::c_void,
                    21,
                    20,
                );
                leanh::lean_closure_set(v___f_3326_, 0, v_froms_3311_);
                leanh::lean_closure_set(v___f_3326_, 1, v_tos_3310_);
                leanh::lean_closure_set(v___f_3326_, 2, v_toPure_3238_);
                leanh::lean_closure_set(v___f_3326_, 3, v___x_3312_);
                leanh::lean_closure_set(v___f_3326_, 4, v_inst_3255_);
                leanh::lean_closure_set(v___f_3326_, 5, v_inst_3239_);
                leanh::lean_closure_set(v___f_3326_, 6, v_toBind_3240_);
                leanh::lean_closure_set(v___f_3326_, 7, v___x_3254_);
                leanh::lean_closure_set(v___f_3326_, 8, v___x_3316_);
                leanh::lean_closure_set(v___f_3326_, 9, v___x_3324_);
                leanh::lean_closure_set(v___f_3326_, 10, v_inst_3256_);
                leanh::lean_closure_set(v___f_3326_, 11, v_inst_3257_);
                leanh::lean_closure_set(v___f_3326_, 12, v___x_3319_);
                leanh::lean_closure_set(v___f_3326_, 13, v___x_3321_);
                leanh::lean_closure_set(v___f_3326_, 14, v___x_3323_);
                leanh::lean_closure_set(v___f_3326_, 15, v___f_3322_);
                leanh::lean_closure_set(v___f_3326_, 16, v___x_3304_);
                leanh::lean_closure_set(v___f_3326_, 17, v___x_3325_);
                leanh::lean_closure_set(v___f_3326_, 18, v_ref_3259_);
                leanh::lean_closure_set(v___f_3326_, 19, v___f_3281_);
                v___x_7179__overap_3327_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3304_,
                    v___x_3316_,
                    v___x_3324_,
                    v_ns_3284_,
                );
                v___x_3328_ = leanh::lean_apply_1(v___x_7179__overap_3327_, v_ref_3259_);
                v___x_3329_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3328_,
                    v___f_3326_,
                );
                v___x_3330_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3329_,
                    v___f_3260_,
                );
                return v___x_3330_;
            }
            4 => {
                leanh::lean_inc(v_ref_3259_);
                v___f_3358_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3358_, 0, v___f_3246_);
                leanh::lean_closure_set(v___f_3358_, 1, v_ref_3259_);
                v___x_3359_ = leanh::lean_unsigned_to_nat(0);
                v_ns_3360_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3359_);
                v___x_3361_ = leanh::lean_unsigned_to_nat(2);
                v___x_3362_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3361_);
                leanh::lean_dec(v_stx_3245_);
                v_ids_3363_ = l_Lean_Syntax_getArgs(v___x_3362_);
                leanh::lean_dec(v___x_3362_);
                v___x_3364_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3365_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3365_, 0, v_modifyEnv_3354_);
                leanh::lean_closure_set(v___f_3365_, 1, v___x_3364_);
                v___x_3366_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3366_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3366_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3366_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3366_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3366_, 4, v_getEnv_3353_);
                if v_isShared_3357_ == 0 {
                    leanh::lean_ctor_set(v___x_3356_, 1, v___f_3365_);
                    leanh::lean_ctor_set(v___x_3356_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3356_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___f_3365_);
                    v___x_3368_ = v_reuseFailAlloc_3382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v_inst_3247_);
                v___f_3369_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3369_, 0, v_inst_3247_);
                v___f_3370_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3370_, 0, v_inst_3247_);
                v___x_3371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3371_, 0, v___f_3369_);
                leanh::lean_ctor_set(v___x_3371_, 1, v___f_3370_);
                v___x_3372_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3373_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3364_,
                    v___x_3372_,
                    v_inst_3252_,
                );
                v___f_3374_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3374_, 0, v_inst_3253_);
                leanh::lean_closure_set(v___f_3374_, 1, v___x_3364_);
                leanh::lean_inc_ref_n(v___x_3254_, 2);
                leanh::lean_inc_ref(v___f_3374_);
                v___x_3375_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3374_,
                    v___x_3254_,
                );
                leanh::lean_inc(v___x_3375_);
                leanh::lean_inc_ref(v___x_3373_);
                leanh::lean_inc_ref(v___x_3371_);
                v___x_3376_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3376_, 0, v___x_3371_);
                leanh::lean_ctor_set(v___x_3376_, 1, v___x_3373_);
                leanh::lean_ctor_set(v___x_3376_, 2, v___x_3375_);
                leanh::lean_inc_ref(v___x_3352_);
                leanh::lean_inc_ref(v___x_3376_);
                leanh::lean_inc_ref(v___x_3368_);
                leanh::lean_inc_n(v_toBind_3240_, 2);
                leanh::lean_inc(v_ref_3259_);
                v___f_3377_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed
                        as *mut core::ffi::c_void,
                    20,
                    19,
                );
                leanh::lean_closure_set(v___f_3377_, 0, v_ids_3363_);
                leanh::lean_closure_set(v___f_3377_, 1, v___f_3258_);
                leanh::lean_closure_set(v___f_3377_, 2, v_inst_3239_);
                leanh::lean_closure_set(v___f_3377_, 3, v_ref_3259_);
                leanh::lean_closure_set(v___f_3377_, 4, v_toBind_3240_);
                leanh::lean_closure_set(v___f_3377_, 5, v___f_3358_);
                leanh::lean_closure_set(v___f_3377_, 6, v_toPure_3238_);
                leanh::lean_closure_set(v___f_3377_, 7, v___x_3364_);
                leanh::lean_closure_set(v___f_3377_, 8, v_inst_3255_);
                leanh::lean_closure_set(v___f_3377_, 9, v___x_3254_);
                leanh::lean_closure_set(v___f_3377_, 10, v___x_3368_);
                leanh::lean_closure_set(v___f_3377_, 11, v___x_3376_);
                leanh::lean_closure_set(v___f_3377_, 12, v_inst_3256_);
                leanh::lean_closure_set(v___f_3377_, 13, v_inst_3257_);
                leanh::lean_closure_set(v___f_3377_, 14, v___x_3371_);
                leanh::lean_closure_set(v___f_3377_, 15, v___x_3373_);
                leanh::lean_closure_set(v___f_3377_, 16, v___x_3375_);
                leanh::lean_closure_set(v___f_3377_, 17, v___f_3374_);
                leanh::lean_closure_set(v___f_3377_, 18, v___x_3352_);
                v___x_7223__overap_3378_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3352_,
                    v___x_3368_,
                    v___x_3376_,
                    v_ns_3360_,
                );
                v___x_3379_ = leanh::lean_apply_1(v___x_7223__overap_3378_, v_ref_3259_);
                v___x_3380_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3379_,
                    v___f_3377_,
                );
                v___x_3381_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3380_,
                    v___f_3260_,
                );
                return v___x_3381_;
            }
            6 => {
                leanh::lean_inc(v_ref_3259_);
                v___f_3390_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3390_, 0, v___f_3246_);
                leanh::lean_closure_set(v___f_3390_, 1, v_ref_3259_);
                v___x_3391_ = leanh::lean_unsigned_to_nat(0);
                v_ns_3392_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3391_);
                v___x_3393_ = leanh::lean_unsigned_to_nat(2);
                v___x_3394_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3393_);
                leanh::lean_dec(v_stx_3245_);
                v_ids_3395_ = l_Lean_Syntax_getArgs(v___x_3394_);
                leanh::lean_dec(v___x_3394_);
                v___x_3396_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3397_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3397_, 0, v_modifyEnv_3386_);
                leanh::lean_closure_set(v___f_3397_, 1, v___x_3396_);
                v___x_3398_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3398_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3398_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3398_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3398_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3398_, 4, v_getEnv_3385_);
                if v_isShared_3389_ == 0 {
                    leanh::lean_ctor_set(v___x_3388_, 1, v___f_3397_);
                    leanh::lean_ctor_set(v___x_3388_, 0, v___x_3398_);
                    v___x_3400_ = v___x_3388_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___f_3397_);
                    v___x_3400_ = v_reuseFailAlloc_3414_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc_ref(v_inst_3247_);
                v___f_3401_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3401_, 0, v_inst_3247_);
                v___f_3402_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3402_, 0, v_inst_3247_);
                v___x_3403_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3403_, 0, v___f_3401_);
                leanh::lean_ctor_set(v___x_3403_, 1, v___f_3402_);
                v___x_3404_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3405_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3396_,
                    v___x_3404_,
                    v_inst_3252_,
                );
                v___f_3406_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3406_, 0, v_inst_3253_);
                leanh::lean_closure_set(v___f_3406_, 1, v___x_3396_);
                leanh::lean_inc_ref_n(v___x_3254_, 2);
                leanh::lean_inc_ref(v___f_3406_);
                v___x_3407_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3406_,
                    v___x_3254_,
                );
                leanh::lean_inc(v___x_3407_);
                leanh::lean_inc_ref(v___x_3405_);
                leanh::lean_inc_ref(v___x_3403_);
                v___x_3408_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3408_, 0, v___x_3403_);
                leanh::lean_ctor_set(v___x_3408_, 1, v___x_3405_);
                leanh::lean_ctor_set(v___x_3408_, 2, v___x_3407_);
                leanh::lean_inc(v_ref_3259_);
                leanh::lean_inc_ref(v___x_3384_);
                leanh::lean_inc_ref(v___x_3408_);
                leanh::lean_inc_ref(v___x_3400_);
                leanh::lean_inc_n(v_toBind_3240_, 2);
                v___f_3409_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed
                        as *mut core::ffi::c_void,
                    19,
                    18,
                );
                leanh::lean_closure_set(v___f_3409_, 0, v_toPure_3238_);
                leanh::lean_closure_set(v___f_3409_, 1, v___x_3396_);
                leanh::lean_closure_set(v___f_3409_, 2, v_inst_3255_);
                leanh::lean_closure_set(v___f_3409_, 3, v_inst_3239_);
                leanh::lean_closure_set(v___f_3409_, 4, v_toBind_3240_);
                leanh::lean_closure_set(v___f_3409_, 5, v___x_3254_);
                leanh::lean_closure_set(v___f_3409_, 6, v___x_3400_);
                leanh::lean_closure_set(v___f_3409_, 7, v___x_3408_);
                leanh::lean_closure_set(v___f_3409_, 8, v_inst_3256_);
                leanh::lean_closure_set(v___f_3409_, 9, v_inst_3257_);
                leanh::lean_closure_set(v___f_3409_, 10, v___x_3403_);
                leanh::lean_closure_set(v___f_3409_, 11, v___x_3405_);
                leanh::lean_closure_set(v___f_3409_, 12, v___x_3407_);
                leanh::lean_closure_set(v___f_3409_, 13, v___f_3406_);
                leanh::lean_closure_set(v___f_3409_, 14, v___x_3384_);
                leanh::lean_closure_set(v___f_3409_, 15, v_ids_3395_);
                leanh::lean_closure_set(v___f_3409_, 16, v_ref_3259_);
                leanh::lean_closure_set(v___f_3409_, 17, v___f_3390_);
                v___x_7244__overap_3410_ = l_Lean_resolveNamespace___redArg(
                    v___x_3254_,
                    v___x_3384_,
                    v___x_3400_,
                    v___x_3408_,
                    v_ns_3392_,
                );
                v___x_3411_ = leanh::lean_apply_1(v___x_7244__overap_3410_, v_ref_3259_);
                v___x_3412_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3411_,
                    v___f_3409_,
                );
                v___x_3413_ = leanh::lean_apply_4(
                    v_toBind_3240_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3443_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_3444_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_toBind_3445_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3446_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_3447_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_3448_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3449_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_stx_3450_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_3451_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_3452_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_3453_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_3454_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___f_3455_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_3456_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_inst_3457_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_3458_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___x_3459_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_inst_3460_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_inst_3461_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_inst_3462_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___f_3463_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_ref_3464_: *mut leanh::LeanObject = *_args.add(21);
    let mut v___x_8610__boxed_3465_: u8 = 0;
    let mut v_res_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8610__boxed_3465_ = (leanh::lean_unbox(v___x_3446_) as u8);
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
    mut v_toPure_3467_: *mut leanh::LeanObject,
    mut v_____x_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3469_ = leanh::lean_ctor_get(v_____x_3468_, 0);
    leanh::lean_inc(v_fst_3469_);
    leanh::lean_dec_ref(v_____x_3468_);
    v___x_3470_ =
        leanh::lean_apply_2(v_toPure_3467_, leanh::lean_box(0), v_fst_3469_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(
    mut v_toApplicative_3480_: *mut leanh::LeanObject,
    mut v_stx_3481_: *mut leanh::LeanObject,
    mut v_____do__lift_3482_: *mut leanh::LeanObject,
    mut v_inst_3483_: *mut leanh::LeanObject,
    mut v_toBind_3484_: *mut leanh::LeanObject,
    mut v___f_3485_: *mut leanh::LeanObject,
    mut v_inst_3486_: *mut leanh::LeanObject,
    mut v_inst_3487_: *mut leanh::LeanObject,
    mut v_inst_3488_: *mut leanh::LeanObject,
    mut v___f_3489_: *mut leanh::LeanObject,
    mut v___f_3490_: *mut leanh::LeanObject,
    mut v_inst_3491_: *mut leanh::LeanObject,
    mut v_inst_3492_: *mut leanh::LeanObject,
    mut v___x_3493_: *mut leanh::LeanObject,
    mut v_inst_3494_: *mut leanh::LeanObject,
    mut v_inst_3495_: *mut leanh::LeanObject,
    mut v_inst_3496_: *mut leanh::LeanObject,
    mut v___f_3497_: *mut leanh::LeanObject,
    mut v_____do__lift_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3499_ = leanh::lean_ctor_get(v_toApplicative_3480_, 1);
    leanh::lean_inc_n(v_toPure_3499_, 2);
    leanh::lean_dec_ref(v_toApplicative_3480_);
    v___x_3500_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0;
    v___x_3501_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1;
    v___x_3502_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2;
    v___x_3503_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4;
    leanh::lean_inc(v_stx_3481_);
    v___x_3504_ = l_Lean_Syntax_isOfKind(v_stx_3481_, v___x_3503_);
    v___x_3505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3505_, 0, v_____do__lift_3482_);
    leanh::lean_ctor_set(v___x_3505_, 1, v_____do__lift_3498_);
    v___x_3506_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_3506_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3506_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3506_, 2, v___x_3505_);
    leanh::lean_inc(v_inst_3483_);
    v___x_3507_ = leanh::lean_apply_2(v_inst_3483_, leanh::lean_box(0), v___x_3506_);
    v___x_3508_ = leanh::lean_box((v___x_3504_) as usize);
    leanh::lean_inc_n(v_toBind_3484_, 2);
    v___f_3509_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed as *mut core::ffi::c_void,
        22,
        21,
    );
    leanh::lean_closure_set(v___f_3509_, 0, v_toPure_3499_);
    leanh::lean_closure_set(v___f_3509_, 1, v_inst_3483_);
    leanh::lean_closure_set(v___f_3509_, 2, v_toBind_3484_);
    leanh::lean_closure_set(v___f_3509_, 3, v___x_3508_);
    leanh::lean_closure_set(v___f_3509_, 4, v___x_3500_);
    leanh::lean_closure_set(v___f_3509_, 5, v___x_3501_);
    leanh::lean_closure_set(v___f_3509_, 6, v___x_3502_);
    leanh::lean_closure_set(v___f_3509_, 7, v_stx_3481_);
    leanh::lean_closure_set(v___f_3509_, 8, v___f_3485_);
    leanh::lean_closure_set(v___f_3509_, 9, v_inst_3486_);
    leanh::lean_closure_set(v___f_3509_, 10, v_inst_3487_);
    leanh::lean_closure_set(v___f_3509_, 11, v_inst_3488_);
    leanh::lean_closure_set(v___f_3509_, 12, v___f_3489_);
    leanh::lean_closure_set(v___f_3509_, 13, v___f_3490_);
    leanh::lean_closure_set(v___f_3509_, 14, v_inst_3491_);
    leanh::lean_closure_set(v___f_3509_, 15, v_inst_3492_);
    leanh::lean_closure_set(v___f_3509_, 16, v___x_3493_);
    leanh::lean_closure_set(v___f_3509_, 17, v_inst_3494_);
    leanh::lean_closure_set(v___f_3509_, 18, v_inst_3495_);
    leanh::lean_closure_set(v___f_3509_, 19, v_inst_3496_);
    leanh::lean_closure_set(v___f_3509_, 20, v___f_3497_);
    v___f_3510_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3510_, 0, v_toPure_3499_);
    v___x_3511_ = leanh::lean_apply_4(
        v_toBind_3484_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3507_,
        v___f_3509_,
    );
    v___x_3512_ = leanh::lean_apply_4(
        v_toBind_3484_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3511_,
        v___f_3510_,
    );
    return v___x_3512_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3513_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_stx_3514_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_3515_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_3516_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_toBind_3517_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___f_3518_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_3519_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_3520_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_3521_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_3522_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___f_3523_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_3524_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_inst_3525_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_3526_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_inst_3527_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_3528_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_inst_3529_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_3530_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_3531_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_3533_: *mut leanh::LeanObject,
    mut v_stx_3534_: *mut leanh::LeanObject,
    mut v_inst_3535_: *mut leanh::LeanObject,
    mut v_toBind_3536_: *mut leanh::LeanObject,
    mut v___f_3537_: *mut leanh::LeanObject,
    mut v_inst_3538_: *mut leanh::LeanObject,
    mut v_inst_3539_: *mut leanh::LeanObject,
    mut v_inst_3540_: *mut leanh::LeanObject,
    mut v___f_3541_: *mut leanh::LeanObject,
    mut v___f_3542_: *mut leanh::LeanObject,
    mut v_inst_3543_: *mut leanh::LeanObject,
    mut v_inst_3544_: *mut leanh::LeanObject,
    mut v___x_3545_: *mut leanh::LeanObject,
    mut v_inst_3546_: *mut leanh::LeanObject,
    mut v_inst_3547_: *mut leanh::LeanObject,
    mut v_inst_3548_: *mut leanh::LeanObject,
    mut v___f_3549_: *mut leanh::LeanObject,
    mut v_getCurrNamespace_3550_: *mut leanh::LeanObject,
    mut v_____do__lift_3551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_3536_);
    v___f_3552_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    leanh::lean_closure_set(v___f_3552_, 0, v_toApplicative_3533_);
    leanh::lean_closure_set(v___f_3552_, 1, v_stx_3534_);
    leanh::lean_closure_set(v___f_3552_, 2, v_____do__lift_3551_);
    leanh::lean_closure_set(v___f_3552_, 3, v_inst_3535_);
    leanh::lean_closure_set(v___f_3552_, 4, v_toBind_3536_);
    leanh::lean_closure_set(v___f_3552_, 5, v___f_3537_);
    leanh::lean_closure_set(v___f_3552_, 6, v_inst_3538_);
    leanh::lean_closure_set(v___f_3552_, 7, v_inst_3539_);
    leanh::lean_closure_set(v___f_3552_, 8, v_inst_3540_);
    leanh::lean_closure_set(v___f_3552_, 9, v___f_3541_);
    leanh::lean_closure_set(v___f_3552_, 10, v___f_3542_);
    leanh::lean_closure_set(v___f_3552_, 11, v_inst_3543_);
    leanh::lean_closure_set(v___f_3552_, 12, v_inst_3544_);
    leanh::lean_closure_set(v___f_3552_, 13, v___x_3545_);
    leanh::lean_closure_set(v___f_3552_, 14, v_inst_3546_);
    leanh::lean_closure_set(v___f_3552_, 15, v_inst_3547_);
    leanh::lean_closure_set(v___f_3552_, 16, v_inst_3548_);
    leanh::lean_closure_set(v___f_3552_, 17, v___f_3549_);
    v___x_3553_ = leanh::lean_apply_4(
        v_toBind_3536_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_3550_,
        v___f_3552_,
    );
    return v___x_3553_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3554_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_stx_3555_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_3556_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toBind_3557_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_3558_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_3559_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_3560_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_3561_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_3562_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_3563_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_3564_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_3565_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_3566_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_inst_3567_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_inst_3568_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_3569_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_3570_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_getCurrNamespace_3571_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_3572_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3577_: *mut leanh::LeanObject,
    mut v_inst_3578_: *mut leanh::LeanObject,
    mut v_inst_3579_: *mut leanh::LeanObject,
    mut v_inst_3580_: *mut leanh::LeanObject,
    mut v_inst_3581_: *mut leanh::LeanObject,
    mut v_inst_3582_: *mut leanh::LeanObject,
    mut v_inst_3583_: *mut leanh::LeanObject,
    mut v_inst_3584_: *mut leanh::LeanObject,
    mut v_inst_3585_: *mut leanh::LeanObject,
    mut v_inst_3586_: *mut leanh::LeanObject,
    mut v_stx_3587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3588_ = leanh::lean_ctor_get(v_inst_3577_, 0);
    leanh::lean_inc_ref_n(v_toApplicative_3588_, 2);
    v_toBind_3589_ = leanh::lean_ctor_get(v_inst_3577_, 1);
    leanh::lean_inc_n(v_toBind_3589_, 3);
    v_getCurrNamespace_3590_ = leanh::lean_ctor_get(v_inst_3585_, 0);
    leanh::lean_inc(v_getCurrNamespace_3590_);
    v_getOpenDecls_3591_ = leanh::lean_ctor_get(v_inst_3585_, 1);
    leanh::lean_inc(v_getOpenDecls_3591_);
    leanh::lean_dec_ref(v_inst_3585_);
    v___f_3592_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3592_, 0, v_toApplicative_3588_);
    leanh::lean_inc(v_inst_3582_);
    v___f_3593_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3593_, 0, v_inst_3582_);
    leanh::lean_closure_set(v___f_3593_, 1, v_toBind_3589_);
    leanh::lean_closure_set(v___f_3593_, 2, v___f_3592_);
    v___f_3594_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0;
    v___f_3595_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1;
    v___f_3596_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2;
    leanh::lean_inc_ref(v_inst_3577_);
    v___x_3597_ = l_StateRefT_x27_instMonad___redArg(v_inst_3577_);
    v___f_3598_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    leanh::lean_closure_set(v___f_3598_, 0, v_toApplicative_3588_);
    leanh::lean_closure_set(v___f_3598_, 1, v_stx_3587_);
    leanh::lean_closure_set(v___f_3598_, 2, v_inst_3582_);
    leanh::lean_closure_set(v___f_3598_, 3, v_toBind_3589_);
    leanh::lean_closure_set(v___f_3598_, 4, v___f_3593_);
    leanh::lean_closure_set(v___f_3598_, 5, v_inst_3579_);
    leanh::lean_closure_set(v___f_3598_, 6, v_inst_3577_);
    leanh::lean_closure_set(v___f_3598_, 7, v_inst_3578_);
    leanh::lean_closure_set(v___f_3598_, 8, v___f_3594_);
    leanh::lean_closure_set(v___f_3598_, 9, v___f_3595_);
    leanh::lean_closure_set(v___f_3598_, 10, v_inst_3580_);
    leanh::lean_closure_set(v___f_3598_, 11, v_inst_3581_);
    leanh::lean_closure_set(v___f_3598_, 12, v___x_3597_);
    leanh::lean_closure_set(v___f_3598_, 13, v_inst_3586_);
    leanh::lean_closure_set(v___f_3598_, 14, v_inst_3583_);
    leanh::lean_closure_set(v___f_3598_, 15, v_inst_3584_);
    leanh::lean_closure_set(v___f_3598_, 16, v___f_3596_);
    leanh::lean_closure_set(v___f_3598_, 17, v_getCurrNamespace_3590_);
    v___x_3599_ = leanh::lean_apply_4(
        v_toBind_3589_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getOpenDecls_3591_,
        v___f_3598_,
    );
    return v___x_3599_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl(
    mut v_m_3600_: *mut leanh::LeanObject,
    mut v_inst_3601_: *mut leanh::LeanObject,
    mut v_inst_3602_: *mut leanh::LeanObject,
    mut v_inst_3603_: *mut leanh::LeanObject,
    mut v_inst_3604_: *mut leanh::LeanObject,
    mut v_inst_3605_: *mut leanh::LeanObject,
    mut v_inst_3606_: *mut leanh::LeanObject,
    mut v_inst_3607_: *mut leanh::LeanObject,
    mut v_inst_3608_: *mut leanh::LeanObject,
    mut v_inst_3609_: *mut leanh::LeanObject,
    mut v_inst_3610_: *mut leanh::LeanObject,
    mut v_stx_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_toPure_3614_: *mut leanh::LeanObject,
    mut v_s_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3616_, 0, v_a_3613_);
    leanh::lean_ctor_set(v___x_3616_, 1, v_s_3615_);
    v___x_3617_ =
        leanh::lean_apply_2(v_toPure_3614_, leanh::lean_box(0), v___x_3616_);
    return v___x_3617_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(
    mut v_toPure_3618_: *mut leanh::LeanObject,
    mut v_ref_3619_: *mut leanh::LeanObject,
    mut v_inst_3620_: *mut leanh::LeanObject,
    mut v_toBind_3621_: *mut leanh::LeanObject,
    mut v_a_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3623_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3623_, 0, v_a_3622_);
    leanh::lean_closure_set(v___f_3623_, 1, v_toPure_3618_);
    v___x_3624_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_3624_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3624_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3624_, 2, v_ref_3619_);
    v___x_3625_ = leanh::lean_apply_2(v_inst_3620_, leanh::lean_box(0), v___x_3624_);
    v___x_3626_ = leanh::lean_apply_4(
        v_toBind_3621_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3625_,
        v___f_3623_,
    );
    return v___x_3626_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(
    mut v_toPure_3627_: *mut leanh::LeanObject,
    mut v_inst_3628_: *mut leanh::LeanObject,
    mut v_toBind_3629_: *mut leanh::LeanObject,
    mut v___x_3630_: *mut leanh::LeanObject,
    mut v___x_3631_: *mut leanh::LeanObject,
    mut v___x_3632_: *mut leanh::LeanObject,
    mut v___x_3633_: *mut leanh::LeanObject,
    mut v___x_3634_: *mut leanh::LeanObject,
    mut v___f_3635_: *mut leanh::LeanObject,
    mut v___x_3636_: *mut leanh::LeanObject,
    mut v___x_3637_: *mut leanh::LeanObject,
    mut v___x_3638_: *mut leanh::LeanObject,
    mut v_nss_3639_: *mut leanh::LeanObject,
    mut v_idStx_3640_: *mut leanh::LeanObject,
    mut v_ref_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100__overap_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_3629_);
    leanh::lean_inc(v_ref_3641_);
    v___f_3642_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_3642_, 0, v_toPure_3627_);
    leanh::lean_closure_set(v___f_3642_, 1, v_ref_3641_);
    leanh::lean_closure_set(v___f_3642_, 2, v_inst_3628_);
    leanh::lean_closure_set(v___f_3642_, 3, v_toBind_3629_);
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
    v___x_3644_ = leanh::lean_apply_1(v___x_100__overap_3643_, v_ref_3641_);
    v___x_3645_ = leanh::lean_apply_4(
        v_toBind_3629_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3644_,
        v___f_3642_,
    );
    return v___x_3645_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(
    mut v_toPure_3646_: *mut leanh::LeanObject,
    mut v_____x_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3648_ = leanh::lean_ctor_get(v_____x_3647_, 0);
    leanh::lean_inc(v_fst_3648_);
    leanh::lean_dec_ref(v_____x_3647_);
    v___x_3649_ =
        leanh::lean_apply_2(v_toPure_3646_, leanh::lean_box(0), v_fst_3648_);
    return v___x_3649_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(
    mut v_toApplicative_3650_: *mut leanh::LeanObject,
    mut v_____do__lift_3651_: *mut leanh::LeanObject,
    mut v_inst_3652_: *mut leanh::LeanObject,
    mut v_toBind_3653_: *mut leanh::LeanObject,
    mut v___x_3654_: *mut leanh::LeanObject,
    mut v___x_3655_: *mut leanh::LeanObject,
    mut v___x_3656_: *mut leanh::LeanObject,
    mut v___x_3657_: *mut leanh::LeanObject,
    mut v___x_3658_: *mut leanh::LeanObject,
    mut v___f_3659_: *mut leanh::LeanObject,
    mut v___x_3660_: *mut leanh::LeanObject,
    mut v___x_3661_: *mut leanh::LeanObject,
    mut v___x_3662_: *mut leanh::LeanObject,
    mut v_nss_3663_: *mut leanh::LeanObject,
    mut v_idStx_3664_: *mut leanh::LeanObject,
    mut v_____do__lift_3665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3666_ = leanh::lean_ctor_get(v_toApplicative_3650_, 1);
    leanh::lean_inc_n(v_toPure_3666_, 2);
    leanh::lean_dec_ref(v_toApplicative_3650_);
    v___x_3667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3667_, 0, v_____do__lift_3651_);
    leanh::lean_ctor_set(v___x_3667_, 1, v_____do__lift_3665_);
    v___x_3668_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_3668_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3668_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3668_, 2, v___x_3667_);
    leanh::lean_inc(v_inst_3652_);
    v___x_3669_ = leanh::lean_apply_2(v_inst_3652_, leanh::lean_box(0), v___x_3668_);
    leanh::lean_inc_n(v_toBind_3653_, 2);
    v___f_3670_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2 as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_3670_, 0, v_toPure_3666_);
    leanh::lean_closure_set(v___f_3670_, 1, v_inst_3652_);
    leanh::lean_closure_set(v___f_3670_, 2, v_toBind_3653_);
    leanh::lean_closure_set(v___f_3670_, 3, v___x_3654_);
    leanh::lean_closure_set(v___f_3670_, 4, v___x_3655_);
    leanh::lean_closure_set(v___f_3670_, 5, v___x_3656_);
    leanh::lean_closure_set(v___f_3670_, 6, v___x_3657_);
    leanh::lean_closure_set(v___f_3670_, 7, v___x_3658_);
    leanh::lean_closure_set(v___f_3670_, 8, v___f_3659_);
    leanh::lean_closure_set(v___f_3670_, 9, v___x_3660_);
    leanh::lean_closure_set(v___f_3670_, 10, v___x_3661_);
    leanh::lean_closure_set(v___f_3670_, 11, v___x_3662_);
    leanh::lean_closure_set(v___f_3670_, 12, v_nss_3663_);
    leanh::lean_closure_set(v___f_3670_, 13, v_idStx_3664_);
    v___f_3671_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3671_, 0, v_toPure_3666_);
    v___x_3672_ = leanh::lean_apply_4(
        v_toBind_3653_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3669_,
        v___f_3670_,
    );
    v___x_3673_ = leanh::lean_apply_4(
        v_toBind_3653_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3672_,
        v___f_3671_,
    );
    return v___x_3673_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(
    mut v_toApplicative_3674_: *mut leanh::LeanObject,
    mut v_inst_3675_: *mut leanh::LeanObject,
    mut v_toBind_3676_: *mut leanh::LeanObject,
    mut v___x_3677_: *mut leanh::LeanObject,
    mut v___x_3678_: *mut leanh::LeanObject,
    mut v___x_3679_: *mut leanh::LeanObject,
    mut v___x_3680_: *mut leanh::LeanObject,
    mut v___x_3681_: *mut leanh::LeanObject,
    mut v___f_3682_: *mut leanh::LeanObject,
    mut v___x_3683_: *mut leanh::LeanObject,
    mut v___x_3684_: *mut leanh::LeanObject,
    mut v___x_3685_: *mut leanh::LeanObject,
    mut v_nss_3686_: *mut leanh::LeanObject,
    mut v_idStx_3687_: *mut leanh::LeanObject,
    mut v_getCurrNamespace_3688_: *mut leanh::LeanObject,
    mut v_____do__lift_3689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_3676_);
    v___f_3690_ = leanh::lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4 as *mut core::ffi::c_void,
        16,
        15,
    );
    leanh::lean_closure_set(v___f_3690_, 0, v_toApplicative_3674_);
    leanh::lean_closure_set(v___f_3690_, 1, v_____do__lift_3689_);
    leanh::lean_closure_set(v___f_3690_, 2, v_inst_3675_);
    leanh::lean_closure_set(v___f_3690_, 3, v_toBind_3676_);
    leanh::lean_closure_set(v___f_3690_, 4, v___x_3677_);
    leanh::lean_closure_set(v___f_3690_, 5, v___x_3678_);
    leanh::lean_closure_set(v___f_3690_, 6, v___x_3679_);
    leanh::lean_closure_set(v___f_3690_, 7, v___x_3680_);
    leanh::lean_closure_set(v___f_3690_, 8, v___x_3681_);
    leanh::lean_closure_set(v___f_3690_, 9, v___f_3682_);
    leanh::lean_closure_set(v___f_3690_, 10, v___x_3683_);
    leanh::lean_closure_set(v___f_3690_, 11, v___x_3684_);
    leanh::lean_closure_set(v___f_3690_, 12, v___x_3685_);
    leanh::lean_closure_set(v___f_3690_, 13, v_nss_3686_);
    leanh::lean_closure_set(v___f_3690_, 14, v_idStx_3687_);
    v___x_3691_ = leanh::lean_apply_4(
        v_toBind_3676_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_3688_,
        v___f_3690_,
    );
    return v___x_3691_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(
    mut v_inst_3692_: *mut leanh::LeanObject,
    mut v_inst_3693_: *mut leanh::LeanObject,
    mut v_inst_3694_: *mut leanh::LeanObject,
    mut v_inst_3695_: *mut leanh::LeanObject,
    mut v_inst_3696_: *mut leanh::LeanObject,
    mut v_inst_3697_: *mut leanh::LeanObject,
    mut v_inst_3698_: *mut leanh::LeanObject,
    mut v_inst_3699_: *mut leanh::LeanObject,
    mut v_inst_3700_: *mut leanh::LeanObject,
    mut v_nss_3701_: *mut leanh::LeanObject,
    mut v_idStx_3702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3703_ = leanh::lean_ctor_get(v_inst_3692_, 0);
                leanh::lean_inc_ref(v_toApplicative_3703_);
                v_toBind_3704_ = leanh::lean_ctor_get(v_inst_3692_, 1);
                leanh::lean_inc(v_toBind_3704_);
                v_getCurrNamespace_3705_ = leanh::lean_ctor_get(v_inst_3700_, 0);
                v_getOpenDecls_3706_ = leanh::lean_ctor_get(v_inst_3700_, 1);
                v_isSharedCheck_3737_ = (!leanh::lean_is_exclusive(v_inst_3700_)) as u8;
                if v_isSharedCheck_3737_ == 0 {
                    v___x_3708_ = v_inst_3700_;
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_getOpenDecls_3706_);
                    leanh::lean_inc(v_getCurrNamespace_3705_);
                    leanh::lean_dec(v_inst_3700_);
                    v___x_3708_ = leanh::lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_3692_);
                v___x_3710_ = l_StateRefT_x27_instMonad___redArg(v_inst_3692_);
                v_getEnv_3711_ = leanh::lean_ctor_get(v_inst_3693_, 0);
                v_modifyEnv_3712_ = leanh::lean_ctor_get(v_inst_3693_, 1);
                v_isSharedCheck_3736_ = (!leanh::lean_is_exclusive(v_inst_3693_)) as u8;
                if v_isSharedCheck_3736_ == 0 {
                    v___x_3714_ = v_inst_3693_;
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyEnv_3712_);
                    leanh::lean_inc(v_getEnv_3711_);
                    leanh::lean_dec(v_inst_3693_);
                    v___x_3714_ = leanh::lean_box(0);
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3716_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3717_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3717_, 0, v_modifyEnv_3712_);
                leanh::lean_closure_set(v___f_3717_, 1, v___x_3716_);
                v___x_3718_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3718_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3718_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3718_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3718_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3718_, 4, v_getEnv_3711_);
                if v_isShared_3715_ == 0 {
                    leanh::lean_ctor_set(v___x_3714_, 1, v___f_3717_);
                    leanh::lean_ctor_set(v___x_3714_, 0, v___x_3718_);
                    v___x_3720_ = v___x_3714_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___f_3717_);
                    v___x_3720_ = v_reuseFailAlloc_3735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_inst_3694_);
                v___f_3721_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_3721_, 0, v_inst_3694_);
                v___f_3722_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_3722_, 0, v_inst_3694_);
                if v_isShared_3709_ == 0 {
                    leanh::lean_ctor_set(v___x_3708_, 1, v___f_3722_);
                    leanh::lean_ctor_set(v___x_3708_, 0, v___f_3721_);
                    v___x_3724_ = v___x_3708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___f_3721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___f_3722_);
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
                v___f_3727_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3727_, 0, v_inst_3696_);
                leanh::lean_closure_set(v___f_3727_, 1, v___x_3716_);
                leanh::lean_inc_ref(v___x_3710_);
                leanh::lean_inc_ref(v___f_3727_);
                v___x_3728_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3727_,
                    v___x_3710_,
                );
                v___x_3729_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3716_, v_inst_3698_);
                v___x_3730_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_3730_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3730_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3730_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3730_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3730_, 4, v_inst_3699_);
                leanh::lean_inc(v_inst_3697_);
                v___x_3731_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3692_, v_inst_3697_);
                leanh::lean_inc(v_toBind_3704_);
                v___f_3732_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                leanh::lean_closure_set(v___f_3732_, 0, v_toApplicative_3703_);
                leanh::lean_closure_set(v___f_3732_, 1, v_inst_3697_);
                leanh::lean_closure_set(v___f_3732_, 2, v_toBind_3704_);
                leanh::lean_closure_set(v___f_3732_, 3, v___x_3710_);
                leanh::lean_closure_set(v___f_3732_, 4, v___x_3720_);
                leanh::lean_closure_set(v___f_3732_, 5, v___x_3724_);
                leanh::lean_closure_set(v___f_3732_, 6, v___x_3726_);
                leanh::lean_closure_set(v___f_3732_, 7, v___x_3728_);
                leanh::lean_closure_set(v___f_3732_, 8, v___f_3727_);
                leanh::lean_closure_set(v___f_3732_, 9, v___x_3729_);
                leanh::lean_closure_set(v___f_3732_, 10, v___x_3730_);
                leanh::lean_closure_set(v___f_3732_, 11, v___x_3731_);
                leanh::lean_closure_set(v___f_3732_, 12, v_nss_3701_);
                leanh::lean_closure_set(v___f_3732_, 13, v_idStx_3702_);
                leanh::lean_closure_set(v___f_3732_, 14, v_getCurrNamespace_3705_);
                v___x_3733_ = leanh::lean_apply_4(
                    v_toBind_3704_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_m_3738_: *mut leanh::LeanObject,
    mut v_inst_3739_: *mut leanh::LeanObject,
    mut v_inst_3740_: *mut leanh::LeanObject,
    mut v_inst_3741_: *mut leanh::LeanObject,
    mut v_inst_3742_: *mut leanh::LeanObject,
    mut v_inst_3743_: *mut leanh::LeanObject,
    mut v_inst_3744_: *mut leanh::LeanObject,
    mut v_inst_3745_: *mut leanh::LeanObject,
    mut v_inst_3746_: *mut leanh::LeanObject,
    mut v_inst_3747_: *mut leanh::LeanObject,
    mut v_nss_3748_: *mut leanh::LeanObject,
    mut v_idStx_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Elab_Open(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Open(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Open(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Open(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Open(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Open(builtin);
}