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
    initialize_Lean_Parser_Command, meta_initialize_Lean_Parser_Command,
    runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::ResolveName::{
    l_Lean_resolveGlobalConstNoOverloadCore___redArg, l_Lean_resolveNamespace___redArg,
    l_Lean_resolveUniqueNamespace___redArg,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_activateScoped___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value) as *mut LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value) as *mut LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value) as *mut LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value
) as *mut LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value
) as *mut LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_MessageData_ofExpr as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 111, 112, 101, 110, 0]};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value:
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
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
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
        111, 112, 101, 110, 82, 101, 110, 97, 109, 105, 110, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value:
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
    m_data: [111, 112, 101, 110, 83, 99, 111, 112, 101, 100, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value:
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
    m_data: [111, 112, 101, 110, 79, 110, 108, 121, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value:
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
    m_data: [111, 112, 101, 110, 72, 105, 100, 105, 110, 103, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value:
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
    m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value:
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
    m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value:
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
    m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value:
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
    m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value:
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
    m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value:
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
    m_fun: l_Option_map as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value: LeanCtorObject<
    5,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value:
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
    m_fun: l_Option_bind as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value:
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
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value:
    LeanCtorObject<1> = LeanCtorObject {
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
pub static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value:
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
    m_data: [111, 112, 101, 110, 83, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1:
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2:
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value)
            as *mut LeanObject,
        4840083868155834027 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_TSyntax_getId___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
    mut v_inst_1876_: *mut LeanObject,
    mut v_____do__lift_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = lean_ctor_get(v_inst_1876_, 0);
    lean_inc_ref(v_toApplicative_1879_);
    lean_dec_ref(v_inst_1876_);
    v_currNamespace_1880_ = lean_ctor_get(v_____do__lift_1877_, 1);
    lean_inc(v_currNamespace_1880_);
    lean_dec_ref(v_____do__lift_1877_);
    v_toPure_1881_ = lean_ctor_get(v_toApplicative_1879_, 1);
    lean_inc(v_toPure_1881_);
    lean_dec_ref(v_toApplicative_1879_);
    v___x_1882_ = lean_apply_2(v_toPure_1881_, lean_box(0), v_currNamespace_1880_);
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(
    mut v_inst_1883_: *mut LeanObject,
    mut v_____do__lift_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(
        v_inst_1883_,
        v_____do__lift_1884_,
        v___y_1885_,
    );
    lean_dec(v___y_1885_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
    mut v_inst_1887_: *mut LeanObject,
    mut v_____do__lift_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1890_ = lean_ctor_get(v_inst_1887_, 0);
    lean_inc_ref(v_toApplicative_1890_);
    lean_dec_ref(v_inst_1887_);
    v_openDecls_1891_ = lean_ctor_get(v_____do__lift_1888_, 0);
    lean_inc(v_openDecls_1891_);
    lean_dec_ref(v_____do__lift_1888_);
    v_toPure_1892_ = lean_ctor_get(v_toApplicative_1890_, 1);
    lean_inc(v_toPure_1892_);
    lean_dec_ref(v_toApplicative_1890_);
    v___x_1893_ = lean_apply_2(v_toPure_1892_, lean_box(0), v_openDecls_1891_);
    return v___x_1893_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(
    mut v_inst_1894_: *mut LeanObject,
    mut v_____do__lift_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(
        v_inst_1894_,
        v_____do__lift_1895_,
        v___y_1896_,
    );
    lean_dec(v___y_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
    mut v_inst_1898_: *mut LeanObject,
    mut v_inst_1899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1898_, 3);
    v___f_1900_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1900_, 0, v_inst_1898_);
    v___f_1901_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1901_, 0, v_inst_1898_);
    v___x_1902_ = lean_alloc_closure(l_StateRefT_x27_get___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1902_, 0, lean_box(0));
    lean_closure_set(v___x_1902_, 1, lean_box(0));
    lean_closure_set(v___x_1902_, 2, lean_box(0));
    lean_closure_set(v___x_1902_, 3, v_inst_1899_);
    lean_inc_ref(v___x_1902_);
    v___x_1903_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_1903_, 0, lean_box(0));
    lean_closure_set(v___x_1903_, 1, lean_box(0));
    lean_closure_set(v___x_1903_, 2, lean_box(0));
    lean_closure_set(v___x_1903_, 3, v_inst_1898_);
    lean_closure_set(v___x_1903_, 4, lean_box(0));
    lean_closure_set(v___x_1903_, 5, lean_box(0));
    lean_closure_set(v___x_1903_, 6, v___x_1902_);
    lean_closure_set(v___x_1903_, 7, v___f_1900_);
    v___x_1904_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_1904_, 0, lean_box(0));
    lean_closure_set(v___x_1904_, 1, lean_box(0));
    lean_closure_set(v___x_1904_, 2, lean_box(0));
    lean_closure_set(v___x_1904_, 3, v_inst_1898_);
    lean_closure_set(v___x_1904_, 4, lean_box(0));
    lean_closure_set(v___x_1904_, 5, lean_box(0));
    lean_closure_set(v___x_1904_, 6, v___x_1902_);
    lean_closure_set(v___x_1904_, 7, v___f_1901_);
    v___x_1905_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1905_, 0, v___x_1903_);
    lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_instMonadResolveNameM(
    mut v_m_1906_: *mut LeanObject,
    mut v_inst_1907_: *mut LeanObject,
    mut v_inst_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1907_, v_inst_1908_);
    return v___x_1909_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
    mut v_idStx_1910_: *mut LeanObject,
    mut v_withRef_1911_: *mut LeanObject,
    mut v___x_1912_: *mut LeanObject,
    mut v_oldRef_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1914_ = l_Lean_replaceRef(v_idStx_1910_, v_oldRef_1913_);
    v___x_1915_ = lean_apply_3(v_withRef_1911_, lean_box(0), v_ref_1914_, v___x_1912_);
    return v___x_1915_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(
    mut v_idStx_1916_: *mut LeanObject,
    mut v_withRef_1917_: *mut LeanObject,
    mut v___x_1918_: *mut LeanObject,
    mut v_oldRef_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(
        v_idStx_1916_,
        v_withRef_1917_,
        v___x_1918_,
        v_oldRef_1919_,
    );
    lean_dec(v_oldRef_1919_);
    lean_dec(v_idStx_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(
    mut v_declName_1921_: *mut LeanObject,
    mut v_inst_1922_: *mut LeanObject,
    mut v_inst_1923_: *mut LeanObject,
    mut v_inst_1924_: *mut LeanObject,
    mut v_inst_1925_: *mut LeanObject,
    mut v_inst_1926_: *mut LeanObject,
    mut v_inst_1927_: *mut LeanObject,
    mut v_inst_1928_: *mut LeanObject,
    mut v_inst_1929_: *mut LeanObject,
    mut v_inst_1930_: *mut LeanObject,
    mut v_idStx_1931_: *mut LeanObject,
    mut v_toBind_1932_: *mut LeanObject,
    mut v_toApplicative_1933_: *mut LeanObject,
    mut v_____do__lift_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    v___x_1935_ = 1;
    lean_inc(v_declName_1921_);
    v___x_1936_ = l_Lean_Environment_contains(v_____do__lift_1934_, v_declName_1921_, v___x_1935_);
    if v___x_1936_ == 0 {
        let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_1938_: *mut LeanObject = core::ptr::null_mut();
        let mut v_withRef_1939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1933_);
        lean_inc_ref(v_inst_1923_);
        v___x_1937_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_1937_, 0, v_inst_1922_);
        lean_ctor_set(v___x_1937_, 1, v_inst_1923_);
        lean_ctor_set(v___x_1937_, 2, v_inst_1924_);
        v_getRef_1938_ = lean_ctor_get(v_inst_1923_, 0);
        lean_inc(v_getRef_1938_);
        v_withRef_1939_ = lean_ctor_get(v_inst_1923_, 1);
        lean_inc(v_withRef_1939_);
        lean_dec_ref(v_inst_1923_);
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
        v___f_1941_ = lean_alloc_closure(
            l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1941_, 0, v_idStx_1931_);
        lean_closure_set(v___f_1941_, 1, v_withRef_1939_);
        lean_closure_set(v___f_1941_, 2, v___x_1940_);
        v___x_1942_ = lean_apply_4(
            v_toBind_1932_,
            lean_box(0),
            lean_box(0),
            v_getRef_1938_,
            v___f_1941_,
        );
        return v___x_1942_;
    } else {
        let mut v_toPure_1943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_1932_);
        lean_dec(v_idStx_1931_);
        lean_dec(v_inst_1930_);
        lean_dec_ref(v_inst_1929_);
        lean_dec(v_inst_1928_);
        lean_dec_ref(v_inst_1927_);
        lean_dec_ref(v_inst_1926_);
        lean_dec_ref(v_inst_1925_);
        lean_dec(v_inst_1924_);
        lean_dec_ref(v_inst_1923_);
        lean_dec_ref(v_inst_1922_);
        v_toPure_1943_ = lean_ctor_get(v_toApplicative_1933_, 1);
        lean_inc(v_toPure_1943_);
        lean_dec_ref(v_toApplicative_1933_);
        v___x_1944_ = lean_apply_2(v_toPure_1943_, lean_box(0), v_declName_1921_);
        return v___x_1944_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId___redArg(
    mut v_inst_1945_: *mut LeanObject,
    mut v_inst_1946_: *mut LeanObject,
    mut v_inst_1947_: *mut LeanObject,
    mut v_inst_1948_: *mut LeanObject,
    mut v_inst_1949_: *mut LeanObject,
    mut v_inst_1950_: *mut LeanObject,
    mut v_inst_1951_: *mut LeanObject,
    mut v_inst_1952_: *mut LeanObject,
    mut v_inst_1953_: *mut LeanObject,
    mut v_ns_1954_: *mut LeanObject,
    mut v_idStx_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1956_ = lean_ctor_get(v_inst_1945_, 0);
    lean_inc_ref(v_toApplicative_1956_);
    v_toBind_1957_ = lean_ctor_get(v_inst_1945_, 1);
    lean_inc_n(v_toBind_1957_, 2);
    v_getEnv_1958_ = lean_ctor_get(v_inst_1946_, 0);
    lean_inc(v_getEnv_1958_);
    v___x_1959_ = l_Lean_Syntax_getId(v_idStx_1955_);
    v_declName_1960_ = l_Lean_Name_append(v_ns_1954_, v___x_1959_);
    v___f_1961_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1 as *mut core::ffi::c_void,
        14,
        13,
    );
    lean_closure_set(v___f_1961_, 0, v_declName_1960_);
    lean_closure_set(v___f_1961_, 1, v_inst_1947_);
    lean_closure_set(v___f_1961_, 2, v_inst_1948_);
    lean_closure_set(v___f_1961_, 3, v_inst_1949_);
    lean_closure_set(v___f_1961_, 4, v_inst_1945_);
    lean_closure_set(v___f_1961_, 5, v_inst_1953_);
    lean_closure_set(v___f_1961_, 6, v_inst_1946_);
    lean_closure_set(v___f_1961_, 7, v_inst_1952_);
    lean_closure_set(v___f_1961_, 8, v_inst_1951_);
    lean_closure_set(v___f_1961_, 9, v_inst_1950_);
    lean_closure_set(v___f_1961_, 10, v_idStx_1955_);
    lean_closure_set(v___f_1961_, 11, v_toBind_1957_);
    lean_closure_set(v___f_1961_, 12, v_toApplicative_1956_);
    v___x_1962_ = lean_apply_4(
        v_toBind_1957_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1958_,
        v___f_1961_,
    );
    return v___x_1962_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveId(
    mut v_m_1963_: *mut LeanObject,
    mut v_inst_1964_: *mut LeanObject,
    mut v_inst_1965_: *mut LeanObject,
    mut v_inst_1966_: *mut LeanObject,
    mut v_inst_1967_: *mut LeanObject,
    mut v_inst_1968_: *mut LeanObject,
    mut v_inst_1969_: *mut LeanObject,
    mut v_inst_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
    mut v_ns_1973_: *mut LeanObject,
    mut v_idStx_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_decl_1976_: *mut LeanObject,
    mut v_s_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_openDecls_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_openDecls_1978_ = lean_ctor_get(v_s_1977_, 0);
                v_currNamespace_1979_ = lean_ctor_get(v_s_1977_, 1);
                v_isSharedCheck_1989_ = (!lean_is_exclusive(v_s_1977_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v___x_1981_ = v_s_1977_;
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_currNamespace_1979_);
                    lean_inc(v_openDecls_1978_);
                    lean_dec(v_s_1977_);
                    v___x_1981_ = lean_box(0);
                    v_isShared_1982_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1983_ = lean_box(0);
                v___x_1984_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1984_, 0, v_decl_1976_);
                lean_ctor_set(v___x_1984_, 1, v_openDecls_1978_);
                if v_isShared_1982_ == 0 {
                    lean_ctor_set(v___x_1981_, 0, v___x_1984_);
                    v___x_1986_ = v___x_1981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_currNamespace_1979_);
                    v___x_1986_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1987_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1987_, 0, v___x_1983_);
                lean_ctor_set(v___x_1987_, 1, v___x_1986_);
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
    mut v_inst_1990_: *mut LeanObject,
    mut v_decl_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    v___f_1993_ = lean_alloc_closure(
        l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1993_, 0, v_decl_1991_);
    lean_inc(v_a_1992_);
    v___x_1994_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_1994_, 0, lean_box(0));
    lean_closure_set(v___x_1994_, 1, lean_box(0));
    lean_closure_set(v___x_1994_, 2, lean_box(0));
    lean_closure_set(v___x_1994_, 3, v_a_1992_);
    lean_closure_set(v___x_1994_, 4, v___f_1993_);
    v___x_1995_ = lean_apply_2(v_inst_1990_, lean_box(0), v___x_1994_);
    return v___x_1995_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(
    mut v_inst_1996_: *mut LeanObject,
    mut v_decl_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1999_: *mut LeanObject = core::ptr::null_mut();
    v_res_1999_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_1996_,
        v_decl_1997_,
        v_a_1998_,
    );
    lean_dec(v_a_1998_);
    return v_res_1999_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
    mut v_m_2000_: *mut LeanObject,
    mut v_inst_2001_: *mut LeanObject,
    mut v_decl_2002_: *mut LeanObject,
    mut v_a_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v___x_2004_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2001_,
        v_decl_2002_,
        v_a_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(
    mut v_m_2005_: *mut LeanObject,
    mut v_inst_2006_: *mut LeanObject,
    mut v_decl_2007_: *mut LeanObject,
    mut v_a_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2009_: *mut LeanObject = core::ptr::null_mut();
    v_res_2009_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(
        v_m_2005_,
        v_inst_2006_,
        v_decl_2007_,
        v_a_2008_,
    );
    lean_dec(v_a_2008_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(
    mut v_x_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    v___x_2011_ = lean_box(0);
    v___x_2012_ = l_Lean_mkConst(v_x_2010_, v___x_2011_);
    return v___x_2012_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(
    mut v_toPure_2013_: *mut LeanObject,
    mut v_p_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2015_ = lean_ctor_get(v_p_2014_, 1);
                lean_inc(v_snd_2015_);
                lean_dec_ref(v_p_2014_);
                v_fst_2016_ = lean_ctor_get(v_snd_2015_, 0);
                v_snd_2017_ = lean_ctor_get(v_snd_2015_, 1);
                v_isSharedCheck_2026_ = (!lean_is_exclusive(v_snd_2015_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_2019_ = v_snd_2015_;
                    v_isShared_2020_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2017_);
                    lean_inc(v_fst_2016_);
                    lean_dec(v_snd_2015_);
                    v___x_2019_ = lean_box(0);
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
                    v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fst_2016_);
                    lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_snd_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2023_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2023_, 0, v___x_2022_);
                v___x_2024_ = lean_apply_2(v_toPure_2013_, lean_box(0), v___x_2023_);
                return v___x_2024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(
    mut v_snd_2027_: *mut LeanObject,
    mut v_fst_2028_: *mut LeanObject,
    mut v_toPure_2029_: *mut LeanObject,
    mut v_declName_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = lean_array_push(v_snd_2027_, v_declName_2030_);
    v___x_2032_ = lean_box(0);
    v___x_2033_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2033_, 0, v_fst_2028_);
    lean_ctor_set(v___x_2033_, 1, v___x_2031_);
    v___x_2034_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2034_, 0, v___x_2032_);
    lean_ctor_set(v___x_2034_, 1, v___x_2033_);
    v___x_2035_ = lean_apply_2(v_toPure_2029_, lean_box(0), v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(
    mut v_fst_2036_: *mut LeanObject,
    mut v_snd_2037_: *mut LeanObject,
    mut v_toPure_2038_: *mut LeanObject,
    mut v_ex_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2040_ = lean_array_push(v_fst_2036_, v_ex_2039_);
    v___x_2041_ = lean_box(0);
    v___x_2042_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2042_, 0, v___x_2040_);
    lean_ctor_set(v___x_2042_, 1, v_snd_2037_);
    v___x_2043_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2043_, 0, v___x_2041_);
    lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ = lean_apply_2(v_toPure_2038_, lean_box(0), v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(
    mut v_inst_2045_: *mut LeanObject,
    mut v_toPure_2046_: *mut LeanObject,
    mut v_inst_2047_: *mut LeanObject,
    mut v_inst_2048_: *mut LeanObject,
    mut v_inst_2049_: *mut LeanObject,
    mut v_inst_2050_: *mut LeanObject,
    mut v_inst_2051_: *mut LeanObject,
    mut v_inst_2052_: *mut LeanObject,
    mut v_inst_2053_: *mut LeanObject,
    mut v_inst_2054_: *mut LeanObject,
    mut v_idStx_2055_: *mut LeanObject,
    mut v_toBind_2056_: *mut LeanObject,
    mut v___f_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_x_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2061_ = lean_ctor_get(v___y_2060_, 0);
    lean_inc_n(v_fst_2061_, 2);
    v_snd_2062_ = lean_ctor_get(v___y_2060_, 1);
    lean_inc_n(v_snd_2062_, 2);
    lean_dec_ref(v___y_2060_);
    v_tryCatch_2063_ = lean_ctor_get(v_inst_2045_, 1);
    lean_inc(v_tryCatch_2063_);
    lean_inc(v_toPure_2046_);
    v___f_2064_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2064_, 0, v_snd_2062_);
    lean_closure_set(v___f_2064_, 1, v_fst_2061_);
    lean_closure_set(v___f_2064_, 2, v_toPure_2046_);
    v___f_2065_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2065_, 0, v_fst_2061_);
    lean_closure_set(v___f_2065_, 1, v_snd_2062_);
    lean_closure_set(v___f_2065_, 2, v_toPure_2046_);
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
    lean_inc(v_toBind_2056_);
    v___x_2067_ = lean_apply_4(
        v_toBind_2056_,
        lean_box(0),
        lean_box(0),
        v___x_2066_,
        v___f_2064_,
    );
    v___x_2068_ = lean_apply_3(v_tryCatch_2063_, lean_box(0), v___x_2067_, v___f_2065_);
    v___x_2069_ = lean_apply_4(
        v_toBind_2056_,
        lean_box(0),
        lean_box(0),
        v___x_2068_,
        v___f_2057_,
    );
    return v___x_2069_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11()
-> *mut LeanObject {
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    v___x_2090_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10;
    v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13()
-> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v___x_2093_ =
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12;
    v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(
    mut v_snd_2096_: *mut LeanObject,
    mut v_inst_2097_: *mut LeanObject,
    mut v_inst_2098_: *mut LeanObject,
    mut v_inst_2099_: *mut LeanObject,
    mut v_idStx_2100_: *mut LeanObject,
    mut v___f_2101_: *mut LeanObject,
    mut v_inst_2102_: *mut LeanObject,
    mut v_toBind_2103_: *mut LeanObject,
    mut v___x_2104_: *mut LeanObject,
    mut v_toPure_2105_: *mut LeanObject,
    mut v_____r_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_sz_2117_: usize = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2107_ = lean_array_get_size(v_snd_2096_);
                v___x_2108_ = lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_dec_eq(v___x_2107_, v___x_2108_);
                if v___x_2109_ == 0 {
                    lean_dec(v_toPure_2105_);
                    lean_inc_ref(v_inst_2098_);
                    v___x_2110_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2110_, 0, v_inst_2097_);
                    lean_ctor_set(v___x_2110_, 1, v_inst_2098_);
                    lean_ctor_set(v___x_2110_, 2, v_inst_2099_);
                    v___x_2111_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_getRef_2112_ = lean_ctor_get(v_inst_2098_, 0);
                    v_withRef_2113_ = lean_ctor_get(v_inst_2098_, 1);
                    v_isSharedCheck_2137_ = (!lean_is_exclusive(v_inst_2098_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2115_ = v_inst_2098_;
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_withRef_2113_);
                        lean_inc(v_getRef_2112_);
                        lean_dec(v_inst_2098_);
                        v___x_2115_ = lean_box(0);
                        v_isShared_2116_ = v_isSharedCheck_2137_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_toBind_2103_);
                    lean_dec_ref(v_inst_2102_);
                    lean_dec_ref(v___f_2101_);
                    lean_dec(v_idStx_2100_);
                    lean_dec(v_inst_2099_);
                    lean_dec_ref(v_inst_2098_);
                    lean_dec_ref(v_inst_2097_);
                    v___x_2138_ = lean_array_fget(v_snd_2096_, v___x_2104_);
                    lean_dec(v_snd_2096_);
                    v___x_2139_ = lean_apply_2(v_toPure_2105_, lean_box(0), v___x_2138_);
                    return v___x_2139_;
                }
            }
            1 => {
                v_sz_2117_ = lean_array_size(v_snd_2096_);
                v___x_2118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
                v___x_2119_ = l_Lean_Syntax_getId(v_idStx_2100_);
                v___x_2120_ = l_Lean_MessageData_ofName(v___x_2119_);
                if v_isShared_2116_ == 0 {
                    lean_ctor_set_tag(v___x_2115_, 7);
                    lean_ctor_set(v___x_2115_, 1, v___x_2120_);
                    lean_ctor_set(v___x_2115_, 0, v___x_2118_);
                    v___x_2122_ = v___x_2115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2118_);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2123_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
                v___x_2124_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2124_, 0, v___x_2122_);
                lean_ctor_set(v___x_2124_, 1, v___x_2123_);
                v___x_2125_ = 0usize;
                v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2111_,
                    v___f_2101_,
                    v_sz_2117_,
                    v___x_2125_,
                    v_snd_2096_,
                );
                v___x_2127_ = lean_array_to_list(v___x_2126_);
                v___x_2128_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14;
                v___x_2129_ = lean_box(0);
                v___x_2130_ = l_List_mapTR_loop___redArg(v___x_2128_, v___x_2127_, v___x_2129_);
                v___x_2131_ = l_Lean_MessageData_ofList(v___x_2130_);
                v___x_2132_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2132_, 0, v___x_2124_);
                lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                v___x_2133_ = l_Lean_throwError___redArg(v_inst_2102_, v___x_2110_, v___x_2132_);
                v___f_2134_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2134_, 0, v_idStx_2100_);
                lean_closure_set(v___f_2134_, 1, v_withRef_2113_);
                lean_closure_set(v___f_2134_, 2, v___x_2133_);
                v___x_2135_ = lean_apply_4(
                    v_toBind_2103_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_snd_2140_: *mut LeanObject,
    mut v_inst_2141_: *mut LeanObject,
    mut v_inst_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_idStx_2144_: *mut LeanObject,
    mut v___f_2145_: *mut LeanObject,
    mut v_inst_2146_: *mut LeanObject,
    mut v_toBind_2147_: *mut LeanObject,
    mut v___x_2148_: *mut LeanObject,
    mut v_toPure_2149_: *mut LeanObject,
    mut v_____r_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___x_2148_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(
    mut v___f_2152_: *mut LeanObject,
    mut v_____r_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    v___x_2154_ = lean_apply_1(v___f_2152_, v_____r_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
    mut v_idStx_2155_: *mut LeanObject,
    mut v_withRef_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v_oldRef_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2159_ = l_Lean_replaceRef(v_idStx_2155_, v_oldRef_2158_);
    v___x_2160_ = lean_apply_3(v_withRef_2156_, lean_box(0), v_ref_2159_, v___y_2157_);
    return v___x_2160_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(
    mut v_idStx_2161_: *mut LeanObject,
    mut v_withRef_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v_oldRef_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2165_: *mut LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(
        v_idStx_2161_,
        v_withRef_2162_,
        v___y_2163_,
        v_oldRef_2164_,
    );
    lean_dec(v_oldRef_2164_);
    lean_dec(v_idStx_2161_);
    return v_res_2165_;
}
pub unsafe fn _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2()
-> *mut LeanObject {
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1;
    v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(
    mut v_inst_2171_: *mut LeanObject,
    mut v_inst_2172_: *mut LeanObject,
    mut v_inst_2173_: *mut LeanObject,
    mut v_idStx_2174_: *mut LeanObject,
    mut v___f_2175_: *mut LeanObject,
    mut v_inst_2176_: *mut LeanObject,
    mut v_toBind_2177_: *mut LeanObject,
    mut v___x_2178_: *mut LeanObject,
    mut v_toPure_2179_: *mut LeanObject,
    mut v_nss_2180_: *mut LeanObject,
    mut v_inst_2181_: *mut LeanObject,
    mut v_____s_2182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2183_ = lean_ctor_get(v_____s_2182_, 0);
                lean_inc(v_fst_2183_);
                v_snd_2184_ = lean_ctor_get(v_____s_2182_, 1);
                lean_inc_n(v_snd_2184_, 2);
                lean_dec_ref(v_____s_2182_);
                lean_inc(v_toPure_2179_);
                lean_inc(v___x_2178_);
                lean_inc(v_toBind_2177_);
                lean_inc_ref(v_inst_2176_);
                lean_inc_ref(v___f_2175_);
                lean_inc(v_idStx_2174_);
                lean_inc(v_inst_2173_);
                lean_inc_ref(v_inst_2172_);
                lean_inc_ref(v_inst_2171_);
                v___f_2185_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    11,
                    10,
                );
                lean_closure_set(v___f_2185_, 0, v_snd_2184_);
                lean_closure_set(v___f_2185_, 1, v_inst_2171_);
                lean_closure_set(v___f_2185_, 2, v_inst_2172_);
                lean_closure_set(v___f_2185_, 3, v_inst_2173_);
                lean_closure_set(v___f_2185_, 4, v_idStx_2174_);
                lean_closure_set(v___f_2185_, 5, v___f_2175_);
                lean_closure_set(v___f_2185_, 6, v_inst_2176_);
                lean_closure_set(v___f_2185_, 7, v_toBind_2177_);
                lean_closure_set(v___f_2185_, 8, v___x_2178_);
                lean_closure_set(v___f_2185_, 9, v_toPure_2179_);
                v___x_2186_ = lean_array_get_size(v_fst_2183_);
                v___x_2187_ = l_List_lengthTR___redArg(v_nss_2180_);
                v___x_2188_ = lean_nat_dec_eq(v___x_2186_, v___x_2187_);
                lean_dec(v___x_2187_);
                if v___x_2188_ == 0 {
                    lean_dec_ref(v___f_2185_);
                    lean_dec(v_fst_2183_);
                    lean_dec_ref(v_inst_2181_);
                    v___x_2189_ = lean_box(0);
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
                    lean_dec(v___x_2178_);
                    return v___x_2190_;
                } else {
                    lean_dec(v_snd_2184_);
                    lean_dec(v_toPure_2179_);
                    lean_dec_ref(v___f_2175_);
                    v___f_2191_ = lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2191_, 0, v___f_2185_);
                    v___x_2199_ = lean_unsigned_to_nat(1);
                    v___x_2200_ = lean_nat_dec_eq(v___x_2186_, v___x_2199_);
                    if v___x_2200_ == 0 {
                        lean_dec(v___x_2178_);
                        lean_inc_ref(v_inst_2172_);
                        v___x_2201_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_2201_, 0, v_inst_2171_);
                        lean_ctor_set(v___x_2201_, 1, v_inst_2172_);
                        lean_ctor_set(v___x_2201_, 2, v_inst_2173_);
                        v___x_2202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once), _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
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
                        lean_dec_ref(v_inst_2181_);
                        lean_dec_ref(v_inst_2176_);
                        lean_dec(v_inst_2173_);
                        v_throw_2204_ = lean_ctor_get(v_inst_2171_, 0);
                        lean_inc(v_throw_2204_);
                        lean_dec_ref(v_inst_2171_);
                        v___x_2205_ = lean_array_fget(v_fst_2183_, v___x_2178_);
                        lean_dec(v___x_2178_);
                        lean_dec(v_fst_2183_);
                        v___x_2206_ = lean_apply_2(v_throw_2204_, lean_box(0), v___x_2205_);
                        v___y_2193_ = v___x_2206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_getRef_2194_ = lean_ctor_get(v_inst_2172_, 0);
                lean_inc(v_getRef_2194_);
                v_withRef_2195_ = lean_ctor_get(v_inst_2172_, 1);
                lean_inc(v_withRef_2195_);
                lean_dec_ref(v_inst_2172_);
                v___f_2196_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2196_, 0, v_idStx_2174_);
                lean_closure_set(v___f_2196_, 1, v_withRef_2195_);
                lean_closure_set(v___f_2196_, 2, v___y_2193_);
                lean_inc(v_toBind_2177_);
                v___x_2197_ = lean_apply_4(
                    v_toBind_2177_,
                    lean_box(0),
                    lean_box(0),
                    v_getRef_2194_,
                    v___f_2196_,
                );
                v___x_2198_ = lean_apply_4(
                    v_toBind_2177_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_2207_: *mut LeanObject,
    mut v_inst_2208_: *mut LeanObject,
    mut v_inst_2209_: *mut LeanObject,
    mut v_idStx_2210_: *mut LeanObject,
    mut v___f_2211_: *mut LeanObject,
    mut v_inst_2212_: *mut LeanObject,
    mut v_toBind_2213_: *mut LeanObject,
    mut v___x_2214_: *mut LeanObject,
    mut v_toPure_2215_: *mut LeanObject,
    mut v_nss_2216_: *mut LeanObject,
    mut v_inst_2217_: *mut LeanObject,
    mut v_____s_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2219_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_nss_2216_);
    return v_res_2219_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(
    mut v_inst_2225_: *mut LeanObject,
    mut v_inst_2226_: *mut LeanObject,
    mut v_inst_2227_: *mut LeanObject,
    mut v_inst_2228_: *mut LeanObject,
    mut v_inst_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_inst_2231_: *mut LeanObject,
    mut v_inst_2232_: *mut LeanObject,
    mut v_inst_2233_: *mut LeanObject,
    mut v_nss_2234_: *mut LeanObject,
    mut v_idStx_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2236_ = lean_ctor_get(v_inst_2225_, 0);
    v_toBind_2237_ = lean_ctor_get(v_inst_2225_, 1);
    lean_inc_n(v_toBind_2237_, 3);
    v_toPure_2238_ = lean_ctor_get(v_toApplicative_2236_, 1);
    v___f_2239_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0;
    v___x_2240_ = lean_unsigned_to_nat(0);
    v___x_2241_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2;
    lean_inc_n(v_toPure_2238_, 3);
    v___f_2242_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2242_, 0, v_toPure_2238_);
    lean_inc(v_idStx_2235_);
    lean_inc_ref(v_inst_2231_);
    lean_inc(v_inst_2229_);
    lean_inc_ref(v_inst_2228_);
    lean_inc_ref_n(v_inst_2225_, 2);
    lean_inc_ref(v_inst_2227_);
    v___f_2243_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4
            as *mut core::ffi::c_void,
        16,
        13,
    );
    lean_closure_set(v___f_2243_, 0, v_inst_2227_);
    lean_closure_set(v___f_2243_, 1, v_toPure_2238_);
    lean_closure_set(v___f_2243_, 2, v_inst_2225_);
    lean_closure_set(v___f_2243_, 3, v_inst_2226_);
    lean_closure_set(v___f_2243_, 4, v_inst_2228_);
    lean_closure_set(v___f_2243_, 5, v_inst_2229_);
    lean_closure_set(v___f_2243_, 6, v_inst_2230_);
    lean_closure_set(v___f_2243_, 7, v_inst_2231_);
    lean_closure_set(v___f_2243_, 8, v_inst_2232_);
    lean_closure_set(v___f_2243_, 9, v_inst_2233_);
    lean_closure_set(v___f_2243_, 10, v_idStx_2235_);
    lean_closure_set(v___f_2243_, 11, v_toBind_2237_);
    lean_closure_set(v___f_2243_, 12, v___f_2242_);
    lean_inc(v_nss_2234_);
    v___f_2244_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_2244_, 0, v_inst_2227_);
    lean_closure_set(v___f_2244_, 1, v_inst_2228_);
    lean_closure_set(v___f_2244_, 2, v_inst_2229_);
    lean_closure_set(v___f_2244_, 3, v_idStx_2235_);
    lean_closure_set(v___f_2244_, 4, v___f_2239_);
    lean_closure_set(v___f_2244_, 5, v_inst_2225_);
    lean_closure_set(v___f_2244_, 6, v_toBind_2237_);
    lean_closure_set(v___f_2244_, 7, v___x_2240_);
    lean_closure_set(v___f_2244_, 8, v_toPure_2238_);
    lean_closure_set(v___f_2244_, 9, v_nss_2234_);
    lean_closure_set(v___f_2244_, 10, v_inst_2231_);
    v___x_2245_ =
        l_List_forIn_x27_loop___redArg(v_inst_2225_, v___f_2243_, v_nss_2234_, v___x_2241_);
    lean_dec(v_nss_2234_);
    v___x_2246_ = lean_apply_4(
        v_toBind_2237_,
        lean_box(0),
        lean_box(0),
        v___x_2245_,
        v___f_2244_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(
    mut v_m_2247_: *mut LeanObject,
    mut v_inst_2248_: *mut LeanObject,
    mut v_inst_2249_: *mut LeanObject,
    mut v_inst_2250_: *mut LeanObject,
    mut v_inst_2251_: *mut LeanObject,
    mut v_inst_2252_: *mut LeanObject,
    mut v_inst_2253_: *mut LeanObject,
    mut v_inst_2254_: *mut LeanObject,
    mut v_inst_2255_: *mut LeanObject,
    mut v_inst_2256_: *mut LeanObject,
    mut v_nss_2257_: *mut LeanObject,
    mut v_idStx_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_openDecls_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v_openDecls_2262_ = lean_ctor_get(v_a_2261_, 0);
    lean_inc(v_openDecls_2262_);
    lean_dec_ref(v_a_2261_);
    v_toPure_2263_ = lean_ctor_get(v_toApplicative_2260_, 1);
    lean_inc(v_toPure_2263_);
    lean_dec_ref(v_toApplicative_2260_);
    v___x_2264_ = lean_apply_2(v_toPure_2263_, lean_box(0), v_openDecls_2262_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
    mut v_inst_2265_: *mut LeanObject,
    mut v_toBind_2266_: *mut LeanObject,
    mut v___f_2267_: *mut LeanObject,
    mut v_____r_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2269_);
    v___x_2270_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2270_, 0, lean_box(0));
    lean_closure_set(v___x_2270_, 1, lean_box(0));
    lean_closure_set(v___x_2270_, 2, v___y_2269_);
    v___x_2271_ = lean_apply_2(v_inst_2265_, lean_box(0), v___x_2270_);
    v___x_2272_ = lean_apply_4(
        v_toBind_2266_,
        lean_box(0),
        lean_box(0),
        v___x_2271_,
        v___f_2267_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(
    mut v_inst_2273_: *mut LeanObject,
    mut v_toBind_2274_: *mut LeanObject,
    mut v___f_2275_: *mut LeanObject,
    mut v_____r_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2278_: *mut LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(
        v_inst_2273_,
        v_toBind_2274_,
        v___f_2275_,
        v_____r_2276_,
        v___y_2277_,
    );
    lean_dec(v___y_2277_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(
    mut v_x_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_2280_: *mut LeanObject = core::ptr::null_mut();
    v_snd_2280_ = lean_ctor_get(v_x_2279_, 1);
    lean_inc(v_snd_2280_);
    return v_snd_2280_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(
    mut v_x_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2282_: *mut LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_2281_);
    lean_dec_ref(v_x_2281_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(
    mut v_x_2283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2284_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2284_ = lean_ctor_get(v_x_2283_, 0);
    lean_inc(v_fst_2284_);
    return v_fst_2284_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(
    mut v_x_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_2285_);
    lean_dec_ref(v_x_2285_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(
    mut v_a_2287_: *mut LeanObject,
    mut v_toPure_2288_: *mut LeanObject,
    mut v_s_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    v___x_2290_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2290_, 0, v_a_2287_);
    lean_ctor_set(v___x_2290_, 1, v_s_2289_);
    v___x_2291_ = lean_apply_2(v_toPure_2288_, lean_box(0), v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(
    mut v_toPure_2292_: *mut LeanObject,
    mut v_ref_2293_: *mut LeanObject,
    mut v_inst_2294_: *mut LeanObject,
    mut v_toBind_2295_: *mut LeanObject,
    mut v_a_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    v___f_2297_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2297_, 0, v_a_2296_);
    lean_closure_set(v___f_2297_, 1, v_toPure_2292_);
    v___x_2298_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2298_, 0, lean_box(0));
    lean_closure_set(v___x_2298_, 1, lean_box(0));
    lean_closure_set(v___x_2298_, 2, v_ref_2293_);
    v___x_2299_ = lean_apply_2(v_inst_2294_, lean_box(0), v___x_2298_);
    v___x_2300_ = lean_apply_4(
        v_toBind_2295_,
        lean_box(0),
        lean_box(0),
        v___x_2299_,
        v___f_2297_,
    );
    return v___x_2300_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(
    mut v___f_2301_: *mut LeanObject,
    mut v_ref_2302_: *mut LeanObject,
    mut v_a_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = lean_apply_2(v___f_2301_, v_a_2303_, v_ref_2302_);
    return v___x_2304_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(
    mut v___f_2305_: *mut LeanObject,
    mut v_ref_2306_: *mut LeanObject,
    mut v_a_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2308_ = lean_box(0);
    v___x_2309_ = lean_apply_2(v___f_2305_, v___x_2308_, v_ref_2306_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
    mut v___x_2311_: *mut LeanObject,
    mut v___x_2312_: *mut LeanObject,
    mut v___x_2313_: *mut LeanObject,
    mut v___x_2314_: *mut LeanObject,
    mut v___x_2315_: *mut LeanObject,
    mut v_x_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    v___x_2317_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0;
    v___x_2318_ = l_Lean_Name_mkStr4(v___x_2311_, v___x_2312_, v___x_2313_, v___x_2317_);
    lean_inc(v_x_2316_);
    v___x_2319_ = l_Lean_Syntax_isOfKind(v_x_2316_, v___x_2318_);
    lean_dec(v___x_2318_);
    if v___x_2319_ == 0 {
        let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2316_);
        v___x_2320_ = lean_box(0);
        return v___x_2320_;
    } else {
        let mut v_froms_2321_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tos_2322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
        v_froms_2321_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2314_);
        v_tos_2322_ = l_Lean_Syntax_getArg(v_x_2316_, v___x_2315_);
        lean_dec(v_x_2316_);
        v___x_2323_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2323_, 0, v_froms_2321_);
        lean_ctor_set(v___x_2323_, 1, v_tos_2322_);
        v___x_2324_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2324_, 0, v___x_2323_);
        return v___x_2324_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(
    mut v___x_2325_: *mut LeanObject,
    mut v___x_2326_: *mut LeanObject,
    mut v___x_2327_: *mut LeanObject,
    mut v___x_2328_: *mut LeanObject,
    mut v___x_2329_: *mut LeanObject,
    mut v_x_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(
        v___x_2325_,
        v___x_2326_,
        v___x_2327_,
        v___x_2328_,
        v___x_2329_,
        v_x_2330_,
    );
    lean_dec(v___x_2329_);
    lean_dec(v___x_2328_);
    return v_res_2331_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(
    mut v___x_2332_: *mut LeanObject,
    mut v_toPure_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2335_, 0, v___x_2332_);
    v___x_2336_ = lean_apply_2(v_toPure_2333_, lean_box(0), v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
    mut v_snd_2337_: *mut LeanObject,
    mut v_a_2338_: *mut LeanObject,
    mut v_inst_2339_: *mut LeanObject,
    mut v_toBind_2340_: *mut LeanObject,
    mut v___f_2341_: *mut LeanObject,
    mut v_____r_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Syntax_getId(v_snd_2337_);
    v___x_2345_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2345_, 0, v___x_2344_);
    lean_ctor_set(v___x_2345_, 1, v_a_2338_);
    v___x_2346_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2339_,
        v___x_2345_,
        v___y_2343_,
    );
    v___x_2347_ = lean_apply_4(
        v_toBind_2340_,
        lean_box(0),
        lean_box(0),
        v___x_2346_,
        v___f_2341_,
    );
    return v___x_2347_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(
    mut v_snd_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
    mut v_toBind_2351_: *mut LeanObject,
    mut v___f_2352_: *mut LeanObject,
    mut v_____r_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2355_: *mut LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(
        v_snd_2348_,
        v_a_2349_,
        v_inst_2350_,
        v_toBind_2351_,
        v___f_2352_,
        v_____r_2353_,
        v___y_2354_,
    );
    lean_dec(v___y_2354_);
    lean_dec(v_snd_2348_);
    return v_res_2355_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(
    mut v___f_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v_a_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2357_);
    v___x_2359_ = lean_apply_2(v___f_2356_, v_a_2358_, v___y_2357_);
    return v___x_2359_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(
    mut v___f_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2363_: *mut LeanObject = core::ptr::null_mut();
    v_res_2363_ =
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v___f_2360_, v___y_2361_, v_a_2362_);
    lean_dec(v___y_2361_);
    return v_res_2363_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(
    mut v___x_2364_: *mut LeanObject,
    mut v___x_2365_: *mut LeanObject,
    mut v___x_2366_: *mut LeanObject,
    mut v___x_2367_: *mut LeanObject,
    mut v_snd_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v___x_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v_toBind_2372_: *mut LeanObject,
    mut v___f_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6682__overap_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    v___x_6682__overap_2375_ = l_Lean_Elab_addConstInfo___redArg(
        v___x_2364_,
        v___x_2365_,
        v___x_2366_,
        v___x_2367_,
        v_snd_2368_,
        v_a_2369_,
        v___x_2370_,
    );
    lean_inc(v___y_2371_);
    v___x_2376_ = lean_apply_1(v___x_6682__overap_2375_, v___y_2371_);
    v___x_2377_ = lean_apply_4(
        v_toBind_2372_,
        lean_box(0),
        lean_box(0),
        v___x_2376_,
        v___f_2373_,
    );
    return v___x_2377_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(
    mut v___x_2378_: *mut LeanObject,
    mut v___x_2379_: *mut LeanObject,
    mut v___x_2380_: *mut LeanObject,
    mut v___x_2381_: *mut LeanObject,
    mut v_snd_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v___x_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v_toBind_2386_: *mut LeanObject,
    mut v___f_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2385_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(
    mut v___f_2390_: *mut LeanObject,
    mut v___x_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
    mut v___x_2393_: *mut LeanObject,
    mut v___x_2394_: *mut LeanObject,
    mut v___x_2395_: *mut LeanObject,
    mut v___x_2396_: *mut LeanObject,
    mut v_snd_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_toBind_2399_: *mut LeanObject,
    mut v___f_2400_: *mut LeanObject,
    mut v_fst_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_2403_: u8 = 0;
    v_enabled_2403_ = lean_ctor_get_uint8(
        v_a_2402_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_2403_ == 0 {
        let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_2401_);
        lean_dec(v___f_2400_);
        lean_dec(v_toBind_2399_);
        lean_dec(v_a_2398_);
        lean_dec(v_snd_2397_);
        lean_dec_ref(v___x_2396_);
        lean_dec_ref(v___x_2395_);
        lean_dec_ref(v___x_2394_);
        lean_dec_ref(v___x_2393_);
        lean_inc(v___y_2392_);
        v___x_2404_ = lean_apply_2(v___f_2390_, v___x_2391_, v___y_2392_);
        return v___x_2404_;
    } else {
        let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6697__overap_2407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2390_);
        v___x_2405_ = lean_box(0);
        lean_inc(v_toBind_2399_);
        lean_inc_n(v___y_2392_, 2);
        lean_inc(v_a_2398_);
        lean_inc_ref(v___x_2396_);
        lean_inc_ref(v___x_2395_);
        lean_inc_ref(v___x_2394_);
        lean_inc_ref(v___x_2393_);
        v___f_2406_ = lean_alloc_closure(
            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed as *mut core::ffi::c_void,
            11,
            10,
        );
        lean_closure_set(v___f_2406_, 0, v___x_2393_);
        lean_closure_set(v___f_2406_, 1, v___x_2394_);
        lean_closure_set(v___f_2406_, 2, v___x_2395_);
        lean_closure_set(v___f_2406_, 3, v___x_2396_);
        lean_closure_set(v___f_2406_, 4, v_snd_2397_);
        lean_closure_set(v___f_2406_, 5, v_a_2398_);
        lean_closure_set(v___f_2406_, 6, v___x_2405_);
        lean_closure_set(v___f_2406_, 7, v___y_2392_);
        lean_closure_set(v___f_2406_, 8, v_toBind_2399_);
        lean_closure_set(v___f_2406_, 9, v___f_2400_);
        v___x_6697__overap_2407_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2393_,
            v___x_2394_,
            v___x_2395_,
            v___x_2396_,
            v_fst_2401_,
            v_a_2398_,
            v___x_2405_,
        );
        v___x_2408_ = lean_apply_1(v___x_6697__overap_2407_, v___y_2392_);
        v___x_2409_ = lean_apply_4(
            v_toBind_2399_,
            lean_box(0),
            lean_box(0),
            v___x_2408_,
            v___f_2406_,
        );
        return v___x_2409_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(
    mut v___f_2410_: *mut LeanObject,
    mut v___x_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___x_2413_: *mut LeanObject,
    mut v___x_2414_: *mut LeanObject,
    mut v___x_2415_: *mut LeanObject,
    mut v___x_2416_: *mut LeanObject,
    mut v_snd_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_toBind_2419_: *mut LeanObject,
    mut v___f_2420_: *mut LeanObject,
    mut v_fst_2421_: *mut LeanObject,
    mut v_a_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2423_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2422_);
    lean_dec(v___y_2412_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(
    mut v___x_2424_: *mut LeanObject,
    mut v_inst_2425_: *mut LeanObject,
    mut v_snd_2426_: *mut LeanObject,
    mut v_inst_2427_: *mut LeanObject,
    mut v_toBind_2428_: *mut LeanObject,
    mut v___f_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___x_2431_: *mut LeanObject,
    mut v___x_2432_: *mut LeanObject,
    mut v___x_2433_: *mut LeanObject,
    mut v___x_2434_: *mut LeanObject,
    mut v_fst_2435_: *mut LeanObject,
    mut v_a_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2425_);
    v___x_2437_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2424_, v_inst_2425_);
    v_getInfoState_2438_ = lean_ctor_get(v_inst_2425_, 0);
    lean_inc(v_getInfoState_2438_);
    lean_dec_ref(v_inst_2425_);
    lean_inc_n(v_toBind_2428_, 2);
    lean_inc(v_a_2436_);
    lean_inc(v_snd_2426_);
    v___f_2439_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2439_, 0, v_snd_2426_);
    lean_closure_set(v___f_2439_, 1, v_a_2436_);
    lean_closure_set(v___f_2439_, 2, v_inst_2427_);
    lean_closure_set(v___f_2439_, 3, v_toBind_2428_);
    lean_closure_set(v___f_2439_, 4, v___f_2429_);
    lean_inc_n(v___y_2430_, 2);
    lean_inc_ref(v___f_2439_);
    v___f_2440_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2440_, 0, v___f_2439_);
    lean_closure_set(v___f_2440_, 1, v___y_2430_);
    v___f_2441_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_2441_, 0, v___f_2439_);
    lean_closure_set(v___f_2441_, 1, v___x_2431_);
    lean_closure_set(v___f_2441_, 2, v___y_2430_);
    lean_closure_set(v___f_2441_, 3, v___x_2432_);
    lean_closure_set(v___f_2441_, 4, v___x_2437_);
    lean_closure_set(v___f_2441_, 5, v___x_2433_);
    lean_closure_set(v___f_2441_, 6, v___x_2434_);
    lean_closure_set(v___f_2441_, 7, v_snd_2426_);
    lean_closure_set(v___f_2441_, 8, v_a_2436_);
    lean_closure_set(v___f_2441_, 9, v_toBind_2428_);
    lean_closure_set(v___f_2441_, 10, v___f_2440_);
    lean_closure_set(v___f_2441_, 11, v_fst_2435_);
    v___x_2442_ = lean_apply_4(
        v_toBind_2428_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_2438_,
        v___f_2441_,
    );
    return v___x_2442_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(
    mut v___x_2443_: *mut LeanObject,
    mut v_inst_2444_: *mut LeanObject,
    mut v_snd_2445_: *mut LeanObject,
    mut v_inst_2446_: *mut LeanObject,
    mut v_toBind_2447_: *mut LeanObject,
    mut v___f_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___x_2450_: *mut LeanObject,
    mut v___x_2451_: *mut LeanObject,
    mut v___x_2452_: *mut LeanObject,
    mut v___x_2453_: *mut LeanObject,
    mut v_fst_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2456_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2449_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(
    mut v___x_2457_: *mut LeanObject,
    mut v_inst_2458_: *mut LeanObject,
    mut v_inst_2459_: *mut LeanObject,
    mut v_toBind_2460_: *mut LeanObject,
    mut v___f_2461_: *mut LeanObject,
    mut v___x_2462_: *mut LeanObject,
    mut v___x_2463_: *mut LeanObject,
    mut v___x_2464_: *mut LeanObject,
    mut v___x_2465_: *mut LeanObject,
    mut v_inst_2466_: *mut LeanObject,
    mut v_inst_2467_: *mut LeanObject,
    mut v___x_2468_: *mut LeanObject,
    mut v___x_2469_: *mut LeanObject,
    mut v___x_2470_: *mut LeanObject,
    mut v___f_2471_: *mut LeanObject,
    mut v___x_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
    mut v_a_2474_: *mut LeanObject,
    mut v_x_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738__overap_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2478_ = lean_ctor_get(v_a_2474_, 0);
    lean_inc_n(v_fst_2478_, 2);
    v_snd_2479_ = lean_ctor_get(v_a_2474_, 1);
    lean_inc(v_snd_2479_);
    lean_dec_ref(v_a_2474_);
    lean_inc_ref(v___x_2464_);
    lean_inc_ref(v___x_2463_);
    lean_inc_n(v___y_2477_, 2);
    lean_inc(v_toBind_2460_);
    lean_inc(v___x_2457_);
    v___f_2480_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_2480_, 0, v___x_2457_);
    lean_closure_set(v___f_2480_, 1, v_inst_2458_);
    lean_closure_set(v___f_2480_, 2, v_snd_2479_);
    lean_closure_set(v___f_2480_, 3, v_inst_2459_);
    lean_closure_set(v___f_2480_, 4, v_toBind_2460_);
    lean_closure_set(v___f_2480_, 5, v___f_2461_);
    lean_closure_set(v___f_2480_, 6, v___y_2477_);
    lean_closure_set(v___f_2480_, 7, v___x_2462_);
    lean_closure_set(v___f_2480_, 8, v___x_2463_);
    lean_closure_set(v___f_2480_, 9, v___x_2464_);
    lean_closure_set(v___f_2480_, 10, v___x_2465_);
    lean_closure_set(v___f_2480_, 11, v_fst_2478_);
    v___x_2481_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2457_, v_inst_2466_);
    v___x_2482_ = lean_alloc_closure(l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_2482_, 0, lean_box(0));
    lean_closure_set(v___x_2482_, 1, lean_box(0));
    lean_closure_set(v___x_2482_, 2, lean_box(0));
    lean_closure_set(v___x_2482_, 3, lean_box(0));
    lean_closure_set(v___x_2482_, 4, v_inst_2467_);
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
    v___x_2484_ = lean_apply_1(v___x_6738__overap_2483_, v___y_2477_);
    v___x_2485_ = lean_apply_4(
        v_toBind_2460_,
        lean_box(0),
        lean_box(0),
        v___x_2484_,
        v___f_2480_,
    );
    return v___x_2485_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = *_args.add(0);
    let mut v_inst_2487_: *mut LeanObject = *_args.add(1);
    let mut v_inst_2488_: *mut LeanObject = *_args.add(2);
    let mut v_toBind_2489_: *mut LeanObject = *_args.add(3);
    let mut v___f_2490_: *mut LeanObject = *_args.add(4);
    let mut v___x_2491_: *mut LeanObject = *_args.add(5);
    let mut v___x_2492_: *mut LeanObject = *_args.add(6);
    let mut v___x_2493_: *mut LeanObject = *_args.add(7);
    let mut v___x_2494_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2495_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2496_: *mut LeanObject = *_args.add(10);
    let mut v___x_2497_: *mut LeanObject = *_args.add(11);
    let mut v___x_2498_: *mut LeanObject = *_args.add(12);
    let mut v___x_2499_: *mut LeanObject = *_args.add(13);
    let mut v___f_2500_: *mut LeanObject = *_args.add(14);
    let mut v___x_2501_: *mut LeanObject = *_args.add(15);
    let mut v_a_2502_: *mut LeanObject = *_args.add(16);
    let mut v_a_2503_: *mut LeanObject = *_args.add(17);
    let mut v_x_2504_: *mut LeanObject = *_args.add(18);
    let mut v___y_2505_: *mut LeanObject = *_args.add(19);
    let mut v___y_2506_: *mut LeanObject = *_args.add(20);
    let mut v_res_2507_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2506_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(
    mut v_froms_2508_: *mut LeanObject,
    mut v_tos_2509_: *mut LeanObject,
    mut v_toPure_2510_: *mut LeanObject,
    mut v___x_2511_: *mut LeanObject,
    mut v_inst_2512_: *mut LeanObject,
    mut v_inst_2513_: *mut LeanObject,
    mut v_toBind_2514_: *mut LeanObject,
    mut v___x_2515_: *mut LeanObject,
    mut v___x_2516_: *mut LeanObject,
    mut v___x_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_inst_2519_: *mut LeanObject,
    mut v___x_2520_: *mut LeanObject,
    mut v___x_2521_: *mut LeanObject,
    mut v___x_2522_: *mut LeanObject,
    mut v___f_2523_: *mut LeanObject,
    mut v___x_2524_: *mut LeanObject,
    mut v___x_2525_: usize,
    mut v_ref_2526_: *mut LeanObject,
    mut v___f_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2533_: usize = 0;
    let mut v___x_6759__overap_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Array_zip___redArg(v_froms_2508_, v_tos_2509_);
    v___x_2530_ = lean_box(0);
    v___f_2531_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2531_, 0, v___x_2530_);
    lean_closure_set(v___f_2531_, 1, v_toPure_2510_);
    lean_inc_ref(v___x_2515_);
    lean_inc(v_toBind_2514_);
    v___f_2532_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    lean_closure_set(v___f_2532_, 0, v___x_2511_);
    lean_closure_set(v___f_2532_, 1, v_inst_2512_);
    lean_closure_set(v___f_2532_, 2, v_inst_2513_);
    lean_closure_set(v___f_2532_, 3, v_toBind_2514_);
    lean_closure_set(v___f_2532_, 4, v___f_2531_);
    lean_closure_set(v___f_2532_, 5, v___x_2530_);
    lean_closure_set(v___f_2532_, 6, v___x_2515_);
    lean_closure_set(v___f_2532_, 7, v___x_2516_);
    lean_closure_set(v___f_2532_, 8, v___x_2517_);
    lean_closure_set(v___f_2532_, 9, v_inst_2518_);
    lean_closure_set(v___f_2532_, 10, v_inst_2519_);
    lean_closure_set(v___f_2532_, 11, v___x_2520_);
    lean_closure_set(v___f_2532_, 12, v___x_2521_);
    lean_closure_set(v___f_2532_, 13, v___x_2522_);
    lean_closure_set(v___f_2532_, 14, v___f_2523_);
    lean_closure_set(v___f_2532_, 15, v___x_2524_);
    lean_closure_set(v___f_2532_, 16, v_a_2528_);
    v_sz_2533_ = lean_array_size(v___x_2529_);
    v___x_6759__overap_2534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2515_,
        v___x_2529_,
        v___f_2532_,
        v_sz_2533_,
        v___x_2525_,
        v___x_2530_,
    );
    v___x_2535_ = lean_apply_1(v___x_6759__overap_2534_, v_ref_2526_);
    v___x_2536_ = lean_apply_4(
        v_toBind_2514_,
        lean_box(0),
        lean_box(0),
        v___x_2535_,
        v___f_2527_,
    );
    return v___x_2536_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_froms_2537_: *mut LeanObject = *_args.add(0);
    let mut v_tos_2538_: *mut LeanObject = *_args.add(1);
    let mut v_toPure_2539_: *mut LeanObject = *_args.add(2);
    let mut v___x_2540_: *mut LeanObject = *_args.add(3);
    let mut v_inst_2541_: *mut LeanObject = *_args.add(4);
    let mut v_inst_2542_: *mut LeanObject = *_args.add(5);
    let mut v_toBind_2543_: *mut LeanObject = *_args.add(6);
    let mut v___x_2544_: *mut LeanObject = *_args.add(7);
    let mut v___x_2545_: *mut LeanObject = *_args.add(8);
    let mut v___x_2546_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2547_: *mut LeanObject = *_args.add(10);
    let mut v_inst_2548_: *mut LeanObject = *_args.add(11);
    let mut v___x_2549_: *mut LeanObject = *_args.add(12);
    let mut v___x_2550_: *mut LeanObject = *_args.add(13);
    let mut v___x_2551_: *mut LeanObject = *_args.add(14);
    let mut v___f_2552_: *mut LeanObject = *_args.add(15);
    let mut v___x_2553_: *mut LeanObject = *_args.add(16);
    let mut v___x_2554_: *mut LeanObject = *_args.add(17);
    let mut v_ref_2555_: *mut LeanObject = *_args.add(18);
    let mut v___f_2556_: *mut LeanObject = *_args.add(19);
    let mut v_a_2557_: *mut LeanObject = *_args.add(20);
    let mut v___x_7638__boxed_2558_: usize = 0;
    let mut v_res_2559_: *mut LeanObject = core::ptr::null_mut();
    v___x_7638__boxed_2558_ = lean_unbox_usize(v___x_2554_);
    lean_dec(v___x_2554_);
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
    lean_dec_ref(v_tos_2538_);
    lean_dec_ref(v_froms_2537_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
    mut v___x_2560_: u8,
    mut v___x_2561_: u8,
    mut v_x1_2562_: *mut LeanObject,
    mut v_x2_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v_snd_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v_unused_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_unused_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2564_ = lean_ctor_get(v_x1_2562_, 0);
                v___x_2565_ = (lean_unbox(v_fst_2564_) as u8);
                if v___x_2565_ == 0 {
                    lean_dec(v_x2_2563_);
                    v_snd_2566_ = lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2574_ = (!lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2574_ == 0 {
                        v_unused_2575_ = lean_ctor_get(v_x1_2562_, 0);
                        lean_dec(v_unused_2575_);
                        v___x_2568_ = v_x1_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2566_);
                        lean_dec(v_x1_2562_);
                        v___x_2568_ = lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2574_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2576_ = lean_ctor_get(v_x1_2562_, 1);
                    v_isSharedCheck_2585_ = (!lean_is_exclusive(v_x1_2562_)) as u8;
                    if v_isSharedCheck_2585_ == 0 {
                        v_unused_2586_ = lean_ctor_get(v_x1_2562_, 0);
                        lean_dec(v_unused_2586_);
                        v___x_2578_ = v_x1_2562_;
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_2576_);
                        lean_dec(v_x1_2562_);
                        v___x_2578_ = lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2585_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2570_ = lean_box((v___x_2560_) as usize);
                if v_isShared_2569_ == 0 {
                    lean_ctor_set(v___x_2568_, 0, v___x_2570_);
                    v___x_2572_ = v___x_2568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
                    lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_snd_2566_);
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
                v___x_2581_ = lean_box((v___x_2561_) as usize);
                if v_isShared_2579_ == 0 {
                    lean_ctor_set(v___x_2578_, 1, v___x_2580_);
                    lean_ctor_set(v___x_2578_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2580_);
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
    mut v___x_2587_: *mut LeanObject,
    mut v___x_2588_: *mut LeanObject,
    mut v_x1_2589_: *mut LeanObject,
    mut v_x2_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7682__boxed_2591_: u8 = 0;
    let mut v___x_7683__boxed_2592_: u8 = 0;
    let mut v_res_2593_: *mut LeanObject = core::ptr::null_mut();
    v___x_7682__boxed_2591_ = (lean_unbox(v___x_2587_) as u8);
    v___x_7683__boxed_2592_ = (lean_unbox(v___x_2588_) as u8);
    v_res_2593_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(
        v___x_7682__boxed_2591_,
        v___x_7683__boxed_2592_,
        v_x1_2589_,
        v_x2_2590_,
    );
    return v_res_2593_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(
    mut v_ids_2594_: *mut LeanObject,
    mut v___f_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_inst_2597_: *mut LeanObject,
    mut v_ref_2598_: *mut LeanObject,
    mut v_toBind_2599_: *mut LeanObject,
    mut v___f_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
    v_sz_2603_ = lean_array_size(v_ids_2594_);
    v___x_2604_ = 0usize;
    v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2602_,
        v___f_2595_,
        v_sz_2603_,
        v___x_2604_,
        v_ids_2594_,
    );
    v___x_2606_ = lean_array_to_list(v___x_2605_);
    v___x_2607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2607_, 0, v_a_2596_);
    lean_ctor_set(v___x_2607_, 1, v___x_2606_);
    v___x_2608_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2597_,
        v___x_2607_,
        v_ref_2598_,
    );
    v___x_2609_ = lean_apply_4(
        v_toBind_2599_,
        lean_box(0),
        lean_box(0),
        v___x_2608_,
        v___f_2600_,
    );
    return v___x_2609_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(
    mut v_ids_2610_: *mut LeanObject,
    mut v___f_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_inst_2613_: *mut LeanObject,
    mut v_ref_2614_: *mut LeanObject,
    mut v_toBind_2615_: *mut LeanObject,
    mut v___f_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2618_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_ref_2614_);
    return v_res_2618_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(
    mut v___x_2619_: *mut LeanObject,
    mut v_toPure_2620_: *mut LeanObject,
    mut v___x_2621_: *mut LeanObject,
    mut v___x_2622_: *mut LeanObject,
    mut v___x_2623_: *mut LeanObject,
    mut v___x_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v_toBind_2628_: *mut LeanObject,
    mut v___f_2629_: *mut LeanObject,
    mut v_a_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_2631_: u8 = 0;
    v_enabled_2631_ = lean_ctor_get_uint8(
        v_a_2630_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_2631_ == 0 {
        let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2629_);
        lean_dec(v_toBind_2628_);
        lean_dec(v_a_2626_);
        lean_dec(v_a_2625_);
        lean_dec_ref(v___x_2624_);
        lean_dec_ref(v___x_2623_);
        lean_dec_ref(v___x_2622_);
        lean_dec_ref(v___x_2621_);
        v___x_2632_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2632_, 0, v___x_2619_);
        v___x_2633_ = lean_apply_2(v_toPure_2620_, lean_box(0), v___x_2632_);
        return v___x_2633_;
    } else {
        let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6804__overap_2635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2620_);
        v___x_2634_ = lean_box(0);
        v___x_6804__overap_2635_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2621_,
            v___x_2622_,
            v___x_2623_,
            v___x_2624_,
            v_a_2625_,
            v_a_2626_,
            v___x_2634_,
        );
        lean_inc(v___y_2627_);
        v___x_2636_ = lean_apply_1(v___x_6804__overap_2635_, v___y_2627_);
        v___x_2637_ = lean_apply_4(
            v_toBind_2628_,
            lean_box(0),
            lean_box(0),
            v___x_2636_,
            v___f_2629_,
        );
        return v___x_2637_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(
    mut v___x_2638_: *mut LeanObject,
    mut v_toPure_2639_: *mut LeanObject,
    mut v___x_2640_: *mut LeanObject,
    mut v___x_2641_: *mut LeanObject,
    mut v___x_2642_: *mut LeanObject,
    mut v___x_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v_toBind_2647_: *mut LeanObject,
    mut v___f_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2650_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2649_);
    lean_dec(v___y_2646_);
    return v_res_2650_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(
    mut v___x_2651_: *mut LeanObject,
    mut v_inst_2652_: *mut LeanObject,
    mut v___x_2653_: *mut LeanObject,
    mut v_toPure_2654_: *mut LeanObject,
    mut v___x_2655_: *mut LeanObject,
    mut v___x_2656_: *mut LeanObject,
    mut v___x_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v_toBind_2660_: *mut LeanObject,
    mut v___f_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2652_);
    v___x_2663_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2651_, v_inst_2652_);
    v_getInfoState_2664_ = lean_ctor_get(v_inst_2652_, 0);
    lean_inc(v_getInfoState_2664_);
    lean_dec_ref(v_inst_2652_);
    lean_inc(v_toBind_2660_);
    lean_inc(v___y_2659_);
    v___f_2665_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_2665_, 0, v___x_2653_);
    lean_closure_set(v___f_2665_, 1, v_toPure_2654_);
    lean_closure_set(v___f_2665_, 2, v___x_2655_);
    lean_closure_set(v___f_2665_, 3, v___x_2663_);
    lean_closure_set(v___f_2665_, 4, v___x_2656_);
    lean_closure_set(v___f_2665_, 5, v___x_2657_);
    lean_closure_set(v___f_2665_, 6, v_a_2658_);
    lean_closure_set(v___f_2665_, 7, v_a_2662_);
    lean_closure_set(v___f_2665_, 8, v___y_2659_);
    lean_closure_set(v___f_2665_, 9, v_toBind_2660_);
    lean_closure_set(v___f_2665_, 10, v___f_2661_);
    v___x_2666_ = lean_apply_4(
        v_toBind_2660_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_2664_,
        v___f_2665_,
    );
    return v___x_2666_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(
    mut v___x_2667_: *mut LeanObject,
    mut v_inst_2668_: *mut LeanObject,
    mut v___x_2669_: *mut LeanObject,
    mut v_toPure_2670_: *mut LeanObject,
    mut v___x_2671_: *mut LeanObject,
    mut v___x_2672_: *mut LeanObject,
    mut v___x_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v_toBind_2676_: *mut LeanObject,
    mut v___f_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2679_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2675_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(
    mut v___x_2680_: *mut LeanObject,
    mut v_inst_2681_: *mut LeanObject,
    mut v___x_2682_: *mut LeanObject,
    mut v_toPure_2683_: *mut LeanObject,
    mut v___x_2684_: *mut LeanObject,
    mut v___x_2685_: *mut LeanObject,
    mut v___x_2686_: *mut LeanObject,
    mut v_toBind_2687_: *mut LeanObject,
    mut v___f_2688_: *mut LeanObject,
    mut v_inst_2689_: *mut LeanObject,
    mut v_inst_2690_: *mut LeanObject,
    mut v___x_2691_: *mut LeanObject,
    mut v___x_2692_: *mut LeanObject,
    mut v___x_2693_: *mut LeanObject,
    mut v___f_2694_: *mut LeanObject,
    mut v___x_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_x_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837__overap_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2687_);
    lean_inc_n(v___y_2700_, 2);
    lean_inc(v_a_2697_);
    lean_inc_ref(v___x_2685_);
    lean_inc_ref(v___x_2684_);
    lean_inc(v___x_2680_);
    v___f_2701_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_2701_, 0, v___x_2680_);
    lean_closure_set(v___f_2701_, 1, v_inst_2681_);
    lean_closure_set(v___f_2701_, 2, v___x_2682_);
    lean_closure_set(v___f_2701_, 3, v_toPure_2683_);
    lean_closure_set(v___f_2701_, 4, v___x_2684_);
    lean_closure_set(v___f_2701_, 5, v___x_2685_);
    lean_closure_set(v___f_2701_, 6, v___x_2686_);
    lean_closure_set(v___f_2701_, 7, v_a_2697_);
    lean_closure_set(v___f_2701_, 8, v___y_2700_);
    lean_closure_set(v___f_2701_, 9, v_toBind_2687_);
    lean_closure_set(v___f_2701_, 10, v___f_2688_);
    v___x_2702_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2680_, v_inst_2689_);
    v___x_2703_ = lean_alloc_closure(l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_2703_, 0, lean_box(0));
    lean_closure_set(v___x_2703_, 1, lean_box(0));
    lean_closure_set(v___x_2703_, 2, lean_box(0));
    lean_closure_set(v___x_2703_, 3, lean_box(0));
    lean_closure_set(v___x_2703_, 4, v_inst_2690_);
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
    v___x_2705_ = lean_apply_1(v___x_6837__overap_2704_, v___y_2700_);
    v___x_2706_ = lean_apply_4(
        v_toBind_2687_,
        lean_box(0),
        lean_box(0),
        v___x_2705_,
        v___f_2701_,
    );
    return v___x_2706_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = *_args.add(0);
    let mut v_inst_2708_: *mut LeanObject = *_args.add(1);
    let mut v___x_2709_: *mut LeanObject = *_args.add(2);
    let mut v_toPure_2710_: *mut LeanObject = *_args.add(3);
    let mut v___x_2711_: *mut LeanObject = *_args.add(4);
    let mut v___x_2712_: *mut LeanObject = *_args.add(5);
    let mut v___x_2713_: *mut LeanObject = *_args.add(6);
    let mut v_toBind_2714_: *mut LeanObject = *_args.add(7);
    let mut v___f_2715_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2716_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2717_: *mut LeanObject = *_args.add(10);
    let mut v___x_2718_: *mut LeanObject = *_args.add(11);
    let mut v___x_2719_: *mut LeanObject = *_args.add(12);
    let mut v___x_2720_: *mut LeanObject = *_args.add(13);
    let mut v___f_2721_: *mut LeanObject = *_args.add(14);
    let mut v___x_2722_: *mut LeanObject = *_args.add(15);
    let mut v_a_2723_: *mut LeanObject = *_args.add(16);
    let mut v_a_2724_: *mut LeanObject = *_args.add(17);
    let mut v_x_2725_: *mut LeanObject = *_args.add(18);
    let mut v___y_2726_: *mut LeanObject = *_args.add(19);
    let mut v___y_2727_: *mut LeanObject = *_args.add(20);
    let mut v_res_2728_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2727_);
    return v_res_2728_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(
    mut v_toPure_2729_: *mut LeanObject,
    mut v___x_2730_: *mut LeanObject,
    mut v_inst_2731_: *mut LeanObject,
    mut v___x_2732_: *mut LeanObject,
    mut v___x_2733_: *mut LeanObject,
    mut v___x_2734_: *mut LeanObject,
    mut v_toBind_2735_: *mut LeanObject,
    mut v_inst_2736_: *mut LeanObject,
    mut v_inst_2737_: *mut LeanObject,
    mut v___x_2738_: *mut LeanObject,
    mut v___x_2739_: *mut LeanObject,
    mut v___x_2740_: *mut LeanObject,
    mut v___f_2741_: *mut LeanObject,
    mut v___x_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_ids_2744_: *mut LeanObject,
    mut v_ref_2745_: *mut LeanObject,
    mut v___f_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_6856__overap_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    v___x_2748_ = lean_box(0);
    lean_inc(v_toPure_2729_);
    v___f_2749_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2749_, 0, v___x_2748_);
    lean_closure_set(v___f_2749_, 1, v_toPure_2729_);
    lean_inc(v_toBind_2735_);
    lean_inc_ref(v___x_2732_);
    v___f_2750_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    lean_closure_set(v___f_2750_, 0, v___x_2730_);
    lean_closure_set(v___f_2750_, 1, v_inst_2731_);
    lean_closure_set(v___f_2750_, 2, v___x_2748_);
    lean_closure_set(v___f_2750_, 3, v_toPure_2729_);
    lean_closure_set(v___f_2750_, 4, v___x_2732_);
    lean_closure_set(v___f_2750_, 5, v___x_2733_);
    lean_closure_set(v___f_2750_, 6, v___x_2734_);
    lean_closure_set(v___f_2750_, 7, v_toBind_2735_);
    lean_closure_set(v___f_2750_, 8, v___f_2749_);
    lean_closure_set(v___f_2750_, 9, v_inst_2736_);
    lean_closure_set(v___f_2750_, 10, v_inst_2737_);
    lean_closure_set(v___f_2750_, 11, v___x_2738_);
    lean_closure_set(v___f_2750_, 12, v___x_2739_);
    lean_closure_set(v___f_2750_, 13, v___x_2740_);
    lean_closure_set(v___f_2750_, 14, v___f_2741_);
    lean_closure_set(v___f_2750_, 15, v___x_2742_);
    lean_closure_set(v___f_2750_, 16, v_a_2743_);
    v_sz_2751_ = lean_array_size(v_ids_2744_);
    v___x_2752_ = 0usize;
    v___x_6856__overap_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2732_,
        v_ids_2744_,
        v___f_2750_,
        v_sz_2751_,
        v___x_2752_,
        v___x_2748_,
    );
    v___x_2754_ = lean_apply_1(v___x_6856__overap_2753_, v_ref_2745_);
    v___x_2755_ = lean_apply_4(
        v_toBind_2735_,
        lean_box(0),
        lean_box(0),
        v___x_2754_,
        v___f_2746_,
    );
    return v___x_2755_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_2756_: *mut LeanObject = *_args.add(0);
    let mut v___x_2757_: *mut LeanObject = *_args.add(1);
    let mut v_inst_2758_: *mut LeanObject = *_args.add(2);
    let mut v___x_2759_: *mut LeanObject = *_args.add(3);
    let mut v___x_2760_: *mut LeanObject = *_args.add(4);
    let mut v___x_2761_: *mut LeanObject = *_args.add(5);
    let mut v_toBind_2762_: *mut LeanObject = *_args.add(6);
    let mut v_inst_2763_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2764_: *mut LeanObject = *_args.add(8);
    let mut v___x_2765_: *mut LeanObject = *_args.add(9);
    let mut v___x_2766_: *mut LeanObject = *_args.add(10);
    let mut v___x_2767_: *mut LeanObject = *_args.add(11);
    let mut v___f_2768_: *mut LeanObject = *_args.add(12);
    let mut v___x_2769_: *mut LeanObject = *_args.add(13);
    let mut v_a_2770_: *mut LeanObject = *_args.add(14);
    let mut v_ids_2771_: *mut LeanObject = *_args.add(15);
    let mut v_ref_2772_: *mut LeanObject = *_args.add(16);
    let mut v___f_2773_: *mut LeanObject = *_args.add(17);
    let mut v_a_2774_: *mut LeanObject = *_args.add(18);
    let mut v_res_2775_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_ids_2776_: *mut LeanObject,
    mut v___f_2777_: *mut LeanObject,
    mut v_inst_2778_: *mut LeanObject,
    mut v_ref_2779_: *mut LeanObject,
    mut v_toBind_2780_: *mut LeanObject,
    mut v___f_2781_: *mut LeanObject,
    mut v_toPure_2782_: *mut LeanObject,
    mut v___x_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
    mut v___x_2785_: *mut LeanObject,
    mut v___x_2786_: *mut LeanObject,
    mut v___x_2787_: *mut LeanObject,
    mut v_inst_2788_: *mut LeanObject,
    mut v_inst_2789_: *mut LeanObject,
    mut v___x_2790_: *mut LeanObject,
    mut v___x_2791_: *mut LeanObject,
    mut v___x_2792_: *mut LeanObject,
    mut v___f_2793_: *mut LeanObject,
    mut v___x_2794_: *mut LeanObject,
    mut v_a_2795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876__overap_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_toBind_2780_, 2);
    lean_inc_n(v_ref_2779_, 2);
    lean_inc(v_inst_2778_);
    lean_inc_n(v_a_2795_, 2);
    lean_inc_ref(v_ids_2776_);
    v___f_2796_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2796_, 0, v_ids_2776_);
    lean_closure_set(v___f_2796_, 1, v___f_2777_);
    lean_closure_set(v___f_2796_, 2, v_a_2795_);
    lean_closure_set(v___f_2796_, 3, v_inst_2778_);
    lean_closure_set(v___f_2796_, 4, v_ref_2779_);
    lean_closure_set(v___f_2796_, 5, v_toBind_2780_);
    lean_closure_set(v___f_2796_, 6, v___f_2781_);
    lean_inc_ref(v___x_2786_);
    lean_inc_ref(v___x_2785_);
    lean_inc(v___x_2783_);
    v___f_2797_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    lean_closure_set(v___f_2797_, 0, v_toPure_2782_);
    lean_closure_set(v___f_2797_, 1, v___x_2783_);
    lean_closure_set(v___f_2797_, 2, v_inst_2784_);
    lean_closure_set(v___f_2797_, 3, v___x_2785_);
    lean_closure_set(v___f_2797_, 4, v___x_2786_);
    lean_closure_set(v___f_2797_, 5, v___x_2787_);
    lean_closure_set(v___f_2797_, 6, v_toBind_2780_);
    lean_closure_set(v___f_2797_, 7, v_inst_2788_);
    lean_closure_set(v___f_2797_, 8, v_inst_2789_);
    lean_closure_set(v___f_2797_, 9, v___x_2790_);
    lean_closure_set(v___f_2797_, 10, v___x_2791_);
    lean_closure_set(v___f_2797_, 11, v___x_2792_);
    lean_closure_set(v___f_2797_, 12, v___f_2793_);
    lean_closure_set(v___f_2797_, 13, v___x_2794_);
    lean_closure_set(v___f_2797_, 14, v_a_2795_);
    lean_closure_set(v___f_2797_, 15, v_ids_2776_);
    lean_closure_set(v___f_2797_, 16, v_ref_2779_);
    lean_closure_set(v___f_2797_, 17, v___f_2796_);
    v___f_2798_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2798_, 0, v_inst_2778_);
    lean_closure_set(v___f_2798_, 1, v___x_2783_);
    v___x_6876__overap_2799_ =
        l_Lean_activateScoped___redArg(v___x_2785_, v___x_2786_, v___f_2798_, v_a_2795_);
    v___x_2800_ = lean_apply_1(v___x_6876__overap_2799_, v_ref_2779_);
    v___x_2801_ = lean_apply_4(
        v_toBind_2780_,
        lean_box(0),
        lean_box(0),
        v___x_2800_,
        v___f_2797_,
    );
    return v___x_2801_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ids_2802_: *mut LeanObject = *_args.add(0);
    let mut v___f_2803_: *mut LeanObject = *_args.add(1);
    let mut v_inst_2804_: *mut LeanObject = *_args.add(2);
    let mut v_ref_2805_: *mut LeanObject = *_args.add(3);
    let mut v_toBind_2806_: *mut LeanObject = *_args.add(4);
    let mut v___f_2807_: *mut LeanObject = *_args.add(5);
    let mut v_toPure_2808_: *mut LeanObject = *_args.add(6);
    let mut v___x_2809_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2810_: *mut LeanObject = *_args.add(8);
    let mut v___x_2811_: *mut LeanObject = *_args.add(9);
    let mut v___x_2812_: *mut LeanObject = *_args.add(10);
    let mut v___x_2813_: *mut LeanObject = *_args.add(11);
    let mut v_inst_2814_: *mut LeanObject = *_args.add(12);
    let mut v_inst_2815_: *mut LeanObject = *_args.add(13);
    let mut v___x_2816_: *mut LeanObject = *_args.add(14);
    let mut v___x_2817_: *mut LeanObject = *_args.add(15);
    let mut v___x_2818_: *mut LeanObject = *_args.add(16);
    let mut v___f_2819_: *mut LeanObject = *_args.add(17);
    let mut v___x_2820_: *mut LeanObject = *_args.add(18);
    let mut v_a_2821_: *mut LeanObject = *_args.add(19);
    let mut v_res_2822_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_inst_2825_: *mut LeanObject,
    mut v_toBind_2826_: *mut LeanObject,
    mut v___f_2827_: *mut LeanObject,
    mut v_____r_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_TSyntax_getId(v_a_2823_);
    v___x_2831_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2831_, 0, v___x_2830_);
    lean_ctor_set(v___x_2831_, 1, v_a_2824_);
    v___x_2832_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_2825_,
        v___x_2831_,
        v___y_2829_,
    );
    v___x_2833_ = lean_apply_4(
        v_toBind_2826_,
        lean_box(0),
        lean_box(0),
        v___x_2832_,
        v___f_2827_,
    );
    return v___x_2833_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(
    mut v_a_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_inst_2836_: *mut LeanObject,
    mut v_toBind_2837_: *mut LeanObject,
    mut v___f_2838_: *mut LeanObject,
    mut v_____r_2839_: *mut LeanObject,
    mut v___y_2840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2841_: *mut LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(
        v_a_2834_,
        v_a_2835_,
        v_inst_2836_,
        v_toBind_2837_,
        v___f_2838_,
        v_____r_2839_,
        v___y_2840_,
    );
    lean_dec(v___y_2840_);
    lean_dec(v_a_2834_);
    return v_res_2841_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(
    mut v___f_2842_: *mut LeanObject,
    mut v___x_2843_: *mut LeanObject,
    mut v___y_2844_: *mut LeanObject,
    mut v___x_2845_: *mut LeanObject,
    mut v___x_2846_: *mut LeanObject,
    mut v___x_2847_: *mut LeanObject,
    mut v___x_2848_: *mut LeanObject,
    mut v_a_2849_: *mut LeanObject,
    mut v_a_2850_: *mut LeanObject,
    mut v_toBind_2851_: *mut LeanObject,
    mut v___f_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_2854_: u8 = 0;
    v_enabled_2854_ = lean_ctor_get_uint8(
        v_a_2853_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_2854_ == 0 {
        let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2852_);
        lean_dec(v_toBind_2851_);
        lean_dec(v_a_2850_);
        lean_dec(v_a_2849_);
        lean_dec_ref(v___x_2848_);
        lean_dec_ref(v___x_2847_);
        lean_dec_ref(v___x_2846_);
        lean_dec_ref(v___x_2845_);
        lean_inc(v___y_2844_);
        v___x_2855_ = lean_apply_2(v___f_2842_, v___x_2843_, v___y_2844_);
        return v___x_2855_;
    } else {
        let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6905__overap_2857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2842_);
        v___x_2856_ = lean_box(0);
        v___x_6905__overap_2857_ = l_Lean_Elab_addConstInfo___redArg(
            v___x_2845_,
            v___x_2846_,
            v___x_2847_,
            v___x_2848_,
            v_a_2849_,
            v_a_2850_,
            v___x_2856_,
        );
        lean_inc(v___y_2844_);
        v___x_2858_ = lean_apply_1(v___x_6905__overap_2857_, v___y_2844_);
        v___x_2859_ = lean_apply_4(
            v_toBind_2851_,
            lean_box(0),
            lean_box(0),
            v___x_2858_,
            v___f_2852_,
        );
        return v___x_2859_;
    }
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(
    mut v___f_2860_: *mut LeanObject,
    mut v___x_2861_: *mut LeanObject,
    mut v___y_2862_: *mut LeanObject,
    mut v___x_2863_: *mut LeanObject,
    mut v___x_2864_: *mut LeanObject,
    mut v___x_2865_: *mut LeanObject,
    mut v___x_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_toBind_2869_: *mut LeanObject,
    mut v___f_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2872_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2871_);
    lean_dec(v___y_2862_);
    return v_res_2872_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(
    mut v___x_2873_: *mut LeanObject,
    mut v_inst_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_inst_2876_: *mut LeanObject,
    mut v_toBind_2877_: *mut LeanObject,
    mut v___f_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
    mut v___x_2880_: *mut LeanObject,
    mut v___x_2881_: *mut LeanObject,
    mut v___x_2882_: *mut LeanObject,
    mut v___x_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2874_);
    v___x_2885_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_2873_, v_inst_2874_);
    v_getInfoState_2886_ = lean_ctor_get(v_inst_2874_, 0);
    lean_inc(v_getInfoState_2886_);
    lean_dec_ref(v_inst_2874_);
    lean_inc_n(v_toBind_2877_, 2);
    lean_inc(v_a_2884_);
    lean_inc(v_a_2875_);
    v___f_2887_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2887_, 0, v_a_2875_);
    lean_closure_set(v___f_2887_, 1, v_a_2884_);
    lean_closure_set(v___f_2887_, 2, v_inst_2876_);
    lean_closure_set(v___f_2887_, 3, v_toBind_2877_);
    lean_closure_set(v___f_2887_, 4, v___f_2878_);
    lean_inc_n(v___y_2879_, 2);
    lean_inc_ref(v___f_2887_);
    v___f_2888_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2888_, 0, v___f_2887_);
    lean_closure_set(v___f_2888_, 1, v___y_2879_);
    v___f_2889_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_2889_, 0, v___f_2887_);
    lean_closure_set(v___f_2889_, 1, v___x_2880_);
    lean_closure_set(v___f_2889_, 2, v___y_2879_);
    lean_closure_set(v___f_2889_, 3, v___x_2881_);
    lean_closure_set(v___f_2889_, 4, v___x_2885_);
    lean_closure_set(v___f_2889_, 5, v___x_2882_);
    lean_closure_set(v___f_2889_, 6, v___x_2883_);
    lean_closure_set(v___f_2889_, 7, v_a_2875_);
    lean_closure_set(v___f_2889_, 8, v_a_2884_);
    lean_closure_set(v___f_2889_, 9, v_toBind_2877_);
    lean_closure_set(v___f_2889_, 10, v___f_2888_);
    v___x_2890_ = lean_apply_4(
        v_toBind_2877_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_2886_,
        v___f_2889_,
    );
    return v___x_2890_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(
    mut v___x_2891_: *mut LeanObject,
    mut v_inst_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
    mut v_inst_2894_: *mut LeanObject,
    mut v_toBind_2895_: *mut LeanObject,
    mut v___f_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___x_2898_: *mut LeanObject,
    mut v___x_2899_: *mut LeanObject,
    mut v___x_2900_: *mut LeanObject,
    mut v___x_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2903_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2897_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(
    mut v___x_2904_: *mut LeanObject,
    mut v_inst_2905_: *mut LeanObject,
    mut v_inst_2906_: *mut LeanObject,
    mut v_toBind_2907_: *mut LeanObject,
    mut v___f_2908_: *mut LeanObject,
    mut v___x_2909_: *mut LeanObject,
    mut v___x_2910_: *mut LeanObject,
    mut v___x_2911_: *mut LeanObject,
    mut v___x_2912_: *mut LeanObject,
    mut v_inst_2913_: *mut LeanObject,
    mut v_inst_2914_: *mut LeanObject,
    mut v___x_2915_: *mut LeanObject,
    mut v___x_2916_: *mut LeanObject,
    mut v___x_2917_: *mut LeanObject,
    mut v___f_2918_: *mut LeanObject,
    mut v___x_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_x_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6942__overap_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___x_2911_);
    lean_inc_ref(v___x_2910_);
    lean_inc_n(v___y_2924_, 2);
    lean_inc(v_toBind_2907_);
    lean_inc(v_a_2921_);
    lean_inc(v___x_2904_);
    v___f_2925_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_2925_, 0, v___x_2904_);
    lean_closure_set(v___f_2925_, 1, v_inst_2905_);
    lean_closure_set(v___f_2925_, 2, v_a_2921_);
    lean_closure_set(v___f_2925_, 3, v_inst_2906_);
    lean_closure_set(v___f_2925_, 4, v_toBind_2907_);
    lean_closure_set(v___f_2925_, 5, v___f_2908_);
    lean_closure_set(v___f_2925_, 6, v___y_2924_);
    lean_closure_set(v___f_2925_, 7, v___x_2909_);
    lean_closure_set(v___f_2925_, 8, v___x_2910_);
    lean_closure_set(v___f_2925_, 9, v___x_2911_);
    lean_closure_set(v___f_2925_, 10, v___x_2912_);
    v___x_2926_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2904_, v_inst_2913_);
    v___x_2927_ = lean_alloc_closure(l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_2927_, 0, lean_box(0));
    lean_closure_set(v___x_2927_, 1, lean_box(0));
    lean_closure_set(v___x_2927_, 2, lean_box(0));
    lean_closure_set(v___x_2927_, 3, lean_box(0));
    lean_closure_set(v___x_2927_, 4, v_inst_2914_);
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
    v___x_2929_ = lean_apply_1(v___x_6942__overap_2928_, v___y_2924_);
    v___x_2930_ = lean_apply_4(
        v_toBind_2907_,
        lean_box(0),
        lean_box(0),
        v___x_2929_,
        v___f_2925_,
    );
    return v___x_2930_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2931_: *mut LeanObject = *_args.add(0);
    let mut v_inst_2932_: *mut LeanObject = *_args.add(1);
    let mut v_inst_2933_: *mut LeanObject = *_args.add(2);
    let mut v_toBind_2934_: *mut LeanObject = *_args.add(3);
    let mut v___f_2935_: *mut LeanObject = *_args.add(4);
    let mut v___x_2936_: *mut LeanObject = *_args.add(5);
    let mut v___x_2937_: *mut LeanObject = *_args.add(6);
    let mut v___x_2938_: *mut LeanObject = *_args.add(7);
    let mut v___x_2939_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2940_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2941_: *mut LeanObject = *_args.add(10);
    let mut v___x_2942_: *mut LeanObject = *_args.add(11);
    let mut v___x_2943_: *mut LeanObject = *_args.add(12);
    let mut v___x_2944_: *mut LeanObject = *_args.add(13);
    let mut v___f_2945_: *mut LeanObject = *_args.add(14);
    let mut v___x_2946_: *mut LeanObject = *_args.add(15);
    let mut v_a_2947_: *mut LeanObject = *_args.add(16);
    let mut v_a_2948_: *mut LeanObject = *_args.add(17);
    let mut v_x_2949_: *mut LeanObject = *_args.add(18);
    let mut v___y_2950_: *mut LeanObject = *_args.add(19);
    let mut v___y_2951_: *mut LeanObject = *_args.add(20);
    let mut v_res_2952_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2951_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(
    mut v_toPure_2953_: *mut LeanObject,
    mut v___x_2954_: *mut LeanObject,
    mut v_inst_2955_: *mut LeanObject,
    mut v_inst_2956_: *mut LeanObject,
    mut v_toBind_2957_: *mut LeanObject,
    mut v___x_2958_: *mut LeanObject,
    mut v___x_2959_: *mut LeanObject,
    mut v___x_2960_: *mut LeanObject,
    mut v_inst_2961_: *mut LeanObject,
    mut v_inst_2962_: *mut LeanObject,
    mut v___x_2963_: *mut LeanObject,
    mut v___x_2964_: *mut LeanObject,
    mut v___x_2965_: *mut LeanObject,
    mut v___f_2966_: *mut LeanObject,
    mut v___x_2967_: *mut LeanObject,
    mut v_ids_2968_: *mut LeanObject,
    mut v_ref_2969_: *mut LeanObject,
    mut v___f_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2975_: usize = 0;
    let mut v___x_2976_: usize = 0;
    let mut v___x_6962__overap_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    v___x_2972_ = lean_box(0);
    v___f_2973_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2973_, 0, v___x_2972_);
    lean_closure_set(v___f_2973_, 1, v_toPure_2953_);
    lean_inc_ref(v___x_2958_);
    lean_inc(v_toBind_2957_);
    v___f_2974_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed as *mut core::ffi::c_void,
        21,
        17,
    );
    lean_closure_set(v___f_2974_, 0, v___x_2954_);
    lean_closure_set(v___f_2974_, 1, v_inst_2955_);
    lean_closure_set(v___f_2974_, 2, v_inst_2956_);
    lean_closure_set(v___f_2974_, 3, v_toBind_2957_);
    lean_closure_set(v___f_2974_, 4, v___f_2973_);
    lean_closure_set(v___f_2974_, 5, v___x_2972_);
    lean_closure_set(v___f_2974_, 6, v___x_2958_);
    lean_closure_set(v___f_2974_, 7, v___x_2959_);
    lean_closure_set(v___f_2974_, 8, v___x_2960_);
    lean_closure_set(v___f_2974_, 9, v_inst_2961_);
    lean_closure_set(v___f_2974_, 10, v_inst_2962_);
    lean_closure_set(v___f_2974_, 11, v___x_2963_);
    lean_closure_set(v___f_2974_, 12, v___x_2964_);
    lean_closure_set(v___f_2974_, 13, v___x_2965_);
    lean_closure_set(v___f_2974_, 14, v___f_2966_);
    lean_closure_set(v___f_2974_, 15, v___x_2967_);
    lean_closure_set(v___f_2974_, 16, v_a_2971_);
    v_sz_2975_ = lean_array_size(v_ids_2968_);
    v___x_2976_ = 0usize;
    v___x_6962__overap_2977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2958_,
        v_ids_2968_,
        v___f_2974_,
        v_sz_2975_,
        v___x_2976_,
        v___x_2972_,
    );
    v___x_2978_ = lean_apply_1(v___x_6962__overap_2977_, v_ref_2969_);
    v___x_2979_ = lean_apply_4(
        v_toBind_2957_,
        lean_box(0),
        lean_box(0),
        v___x_2978_,
        v___f_2970_,
    );
    return v___x_2979_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_2980_: *mut LeanObject = *_args.add(0);
    let mut v___x_2981_: *mut LeanObject = *_args.add(1);
    let mut v_inst_2982_: *mut LeanObject = *_args.add(2);
    let mut v_inst_2983_: *mut LeanObject = *_args.add(3);
    let mut v_toBind_2984_: *mut LeanObject = *_args.add(4);
    let mut v___x_2985_: *mut LeanObject = *_args.add(5);
    let mut v___x_2986_: *mut LeanObject = *_args.add(6);
    let mut v___x_2987_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2988_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2989_: *mut LeanObject = *_args.add(9);
    let mut v___x_2990_: *mut LeanObject = *_args.add(10);
    let mut v___x_2991_: *mut LeanObject = *_args.add(11);
    let mut v___x_2992_: *mut LeanObject = *_args.add(12);
    let mut v___f_2993_: *mut LeanObject = *_args.add(13);
    let mut v___x_2994_: *mut LeanObject = *_args.add(14);
    let mut v_ids_2995_: *mut LeanObject = *_args.add(15);
    let mut v_ref_2996_: *mut LeanObject = *_args.add(16);
    let mut v___f_2997_: *mut LeanObject = *_args.add(17);
    let mut v_a_2998_: *mut LeanObject = *_args.add(18);
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_3000_: *mut LeanObject,
    mut v___x_3001_: *mut LeanObject,
    mut v___x_3002_: *mut LeanObject,
    mut v___x_3003_: *mut LeanObject,
    mut v_toBind_3004_: *mut LeanObject,
    mut v___f_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
    mut v_x_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982__overap_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    v___f_3010_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3010_, 0, v_inst_3000_);
    lean_closure_set(v___f_3010_, 1, v___x_3001_);
    v___x_6982__overap_3011_ =
        l_Lean_activateScoped___redArg(v___x_3002_, v___x_3003_, v___f_3010_, v_a_3006_);
    lean_inc(v___y_3009_);
    v___x_3012_ = lean_apply_1(v___x_6982__overap_3011_, v___y_3009_);
    v___x_3013_ = lean_apply_4(
        v_toBind_3004_,
        lean_box(0),
        lean_box(0),
        v___x_3012_,
        v___f_3005_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(
    mut v_inst_3014_: *mut LeanObject,
    mut v___x_3015_: *mut LeanObject,
    mut v___x_3016_: *mut LeanObject,
    mut v___x_3017_: *mut LeanObject,
    mut v_toBind_3018_: *mut LeanObject,
    mut v___f_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_x_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3024_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3023_);
    return v_res_3024_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
    mut v___x_3025_: *mut LeanObject,
    mut v___f_3026_: *mut LeanObject,
    mut v___x_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v_toBind_3029_: *mut LeanObject,
    mut v___f_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6989__overap_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    v___x_6989__overap_3032_ =
        l_List_forIn_x27_loop___redArg(v___x_3025_, v___f_3026_, v_a_3031_, v___x_3027_);
    lean_inc(v___y_3028_);
    v___x_3033_ = lean_apply_1(v___x_6989__overap_3032_, v___y_3028_);
    v___x_3034_ = lean_apply_4(
        v_toBind_3029_,
        lean_box(0),
        lean_box(0),
        v___x_3033_,
        v___f_3030_,
    );
    return v___x_3034_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(
    mut v___x_3035_: *mut LeanObject,
    mut v___f_3036_: *mut LeanObject,
    mut v___x_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v_toBind_3039_: *mut LeanObject,
    mut v___f_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(
        v___x_3035_,
        v___f_3036_,
        v___x_3037_,
        v___y_3038_,
        v_toBind_3039_,
        v___f_3040_,
        v_a_3041_,
    );
    lean_dec(v_a_3041_);
    lean_dec(v___y_3038_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(
    mut v_inst_3045_: *mut LeanObject,
    mut v_inst_3046_: *mut LeanObject,
    mut v_inst_3047_: *mut LeanObject,
    mut v___x_3048_: *mut LeanObject,
    mut v_toBind_3049_: *mut LeanObject,
    mut v___f_3050_: *mut LeanObject,
    mut v___x_3051_: *mut LeanObject,
    mut v___f_3052_: *mut LeanObject,
    mut v_inst_3053_: *mut LeanObject,
    mut v_inst_3054_: *mut LeanObject,
    mut v_inst_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
    mut v_x_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019__overap_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_inst_3046_);
                v___x_3060_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3045_, v_inst_3046_);
                v_getEnv_3061_ = lean_ctor_get(v_inst_3047_, 0);
                v_modifyEnv_3062_ = lean_ctor_get(v_inst_3047_, 1);
                v_isSharedCheck_3085_ = (!lean_is_exclusive(v_inst_3047_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_3064_ = v_inst_3047_;
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyEnv_3062_);
                    lean_inc(v_getEnv_3061_);
                    lean_dec(v_inst_3047_);
                    v___x_3064_ = lean_box(0);
                    v_isShared_3065_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3066_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3067_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3067_, 0, v_modifyEnv_3062_);
                lean_closure_set(v___f_3067_, 1, v___x_3066_);
                v___x_3068_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3068_, 0, lean_box(0));
                lean_closure_set(v___x_3068_, 1, lean_box(0));
                lean_closure_set(v___x_3068_, 2, lean_box(0));
                lean_closure_set(v___x_3068_, 3, lean_box(0));
                lean_closure_set(v___x_3068_, 4, v_getEnv_3061_);
                if v_isShared_3065_ == 0 {
                    lean_ctor_set(v___x_3064_, 1, v___f_3067_);
                    lean_ctor_set(v___x_3064_, 0, v___x_3068_);
                    v___x_3070_ = v___x_3064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3068_);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___f_3067_);
                    v___x_3070_ = v_reuseFailAlloc_3084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_toBind_3049_, 2);
                lean_inc_ref(v___x_3070_);
                lean_inc_ref_n(v___x_3048_, 3);
                v___f_3071_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed
                        as *mut core::ffi::c_void,
                    10,
                    6,
                );
                lean_closure_set(v___f_3071_, 0, v_inst_3046_);
                lean_closure_set(v___f_3071_, 1, v___x_3066_);
                lean_closure_set(v___f_3071_, 2, v___x_3048_);
                lean_closure_set(v___f_3071_, 3, v___x_3070_);
                lean_closure_set(v___f_3071_, 4, v_toBind_3049_);
                lean_closure_set(v___f_3071_, 5, v___f_3050_);
                lean_inc_n(v___y_3059_, 2);
                v___f_3072_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                lean_closure_set(v___f_3072_, 0, v___x_3048_);
                lean_closure_set(v___f_3072_, 1, v___f_3071_);
                lean_closure_set(v___f_3072_, 2, v___x_3051_);
                lean_closure_set(v___f_3072_, 3, v___y_3059_);
                lean_closure_set(v___f_3072_, 4, v_toBind_3049_);
                lean_closure_set(v___f_3072_, 5, v___f_3052_);
                lean_inc_ref(v_inst_3053_);
                v___f_3073_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3073_, 0, v_inst_3053_);
                v___f_3074_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3074_, 0, v_inst_3053_);
                v___x_3075_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3075_, 0, v___f_3073_);
                lean_ctor_set(v___x_3075_, 1, v___f_3074_);
                v___x_3076_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3077_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3066_,
                    v___x_3076_,
                    v_inst_3054_,
                );
                v___f_3078_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3078_, 0, v_inst_3055_);
                lean_closure_set(v___f_3078_, 1, v___x_3066_);
                v___x_3079_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3078_,
                    v___x_3048_,
                );
                v___x_3080_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3080_, 0, v___x_3075_);
                lean_ctor_set(v___x_3080_, 1, v___x_3077_);
                lean_ctor_set(v___x_3080_, 2, v___x_3079_);
                v___x_7019__overap_3081_ = l_Lean_resolveNamespace___redArg(
                    v___x_3048_,
                    v___x_3060_,
                    v___x_3070_,
                    v___x_3080_,
                    v_a_3056_,
                );
                v___x_3082_ = lean_apply_1(v___x_7019__overap_3081_, v___y_3059_);
                v___x_3083_ = lean_apply_4(
                    v_toBind_3049_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_3086_: *mut LeanObject,
    mut v_inst_3087_: *mut LeanObject,
    mut v_inst_3088_: *mut LeanObject,
    mut v___x_3089_: *mut LeanObject,
    mut v_toBind_3090_: *mut LeanObject,
    mut v___f_3091_: *mut LeanObject,
    mut v___x_3092_: *mut LeanObject,
    mut v___f_3093_: *mut LeanObject,
    mut v_inst_3094_: *mut LeanObject,
    mut v_inst_3095_: *mut LeanObject,
    mut v_inst_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_x_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3100_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(
    mut v_inst_3102_: *mut LeanObject,
    mut v___x_3103_: *mut LeanObject,
    mut v___x_3104_: *mut LeanObject,
    mut v___x_3105_: *mut LeanObject,
    mut v_a_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v_toBind_3108_: *mut LeanObject,
    mut v___f_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037__overap_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    v___f_3111_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3111_, 0, v_inst_3102_);
    lean_closure_set(v___f_3111_, 1, v___x_3103_);
    v___x_7037__overap_3112_ =
        l_Lean_activateScoped___redArg(v___x_3104_, v___x_3105_, v___f_3111_, v_a_3106_);
    lean_inc(v___y_3107_);
    v___x_3113_ = lean_apply_1(v___x_7037__overap_3112_, v___y_3107_);
    v___x_3114_ = lean_apply_4(
        v_toBind_3108_,
        lean_box(0),
        lean_box(0),
        v___x_3113_,
        v___f_3109_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(
    mut v_inst_3115_: *mut LeanObject,
    mut v___x_3116_: *mut LeanObject,
    mut v___x_3117_: *mut LeanObject,
    mut v___x_3118_: *mut LeanObject,
    mut v_a_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v_toBind_3121_: *mut LeanObject,
    mut v___f_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3124_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3120_);
    return v_res_3124_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(
    mut v_inst_3125_: *mut LeanObject,
    mut v___x_3126_: *mut LeanObject,
    mut v___x_3127_: *mut LeanObject,
    mut v___x_3128_: *mut LeanObject,
    mut v_toBind_3129_: *mut LeanObject,
    mut v___f_3130_: *mut LeanObject,
    mut v___x_3131_: *mut LeanObject,
    mut v_a_3132_: *mut LeanObject,
    mut v_x_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_3129_);
    lean_inc(v___y_3135_);
    lean_inc(v_a_3132_);
    lean_inc(v_inst_3125_);
    v___f_3136_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_3136_, 0, v_inst_3125_);
    lean_closure_set(v___f_3136_, 1, v___x_3126_);
    lean_closure_set(v___f_3136_, 2, v___x_3127_);
    lean_closure_set(v___f_3136_, 3, v___x_3128_);
    lean_closure_set(v___f_3136_, 4, v_a_3132_);
    lean_closure_set(v___f_3136_, 5, v___y_3135_);
    lean_closure_set(v___f_3136_, 6, v_toBind_3129_);
    lean_closure_set(v___f_3136_, 7, v___f_3130_);
    v___x_3137_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3137_, 0, v_a_3132_);
    lean_ctor_set(v___x_3137_, 1, v___x_3131_);
    v___x_3138_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(
        v_inst_3125_,
        v___x_3137_,
        v___y_3135_,
    );
    v___x_3139_ = lean_apply_4(
        v_toBind_3129_,
        lean_box(0),
        lean_box(0),
        v___x_3138_,
        v___f_3136_,
    );
    return v___x_3139_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(
    mut v_inst_3140_: *mut LeanObject,
    mut v___x_3141_: *mut LeanObject,
    mut v___x_3142_: *mut LeanObject,
    mut v___x_3143_: *mut LeanObject,
    mut v_toBind_3144_: *mut LeanObject,
    mut v___f_3145_: *mut LeanObject,
    mut v___x_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_x_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3151_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3150_);
    return v_res_3151_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(
    mut v_inst_3152_: *mut LeanObject,
    mut v_inst_3153_: *mut LeanObject,
    mut v_inst_3154_: *mut LeanObject,
    mut v___x_3155_: *mut LeanObject,
    mut v_toBind_3156_: *mut LeanObject,
    mut v___f_3157_: *mut LeanObject,
    mut v___x_3158_: *mut LeanObject,
    mut v___x_3159_: *mut LeanObject,
    mut v___f_3160_: *mut LeanObject,
    mut v_inst_3161_: *mut LeanObject,
    mut v_inst_3162_: *mut LeanObject,
    mut v_inst_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_x_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088__overap_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_inst_3153_);
                v___x_3168_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3152_, v_inst_3153_);
                v_getEnv_3169_ = lean_ctor_get(v_inst_3154_, 0);
                v_modifyEnv_3170_ = lean_ctor_get(v_inst_3154_, 1);
                v_isSharedCheck_3193_ = (!lean_is_exclusive(v_inst_3154_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v___x_3172_ = v_inst_3154_;
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyEnv_3170_);
                    lean_inc(v_getEnv_3169_);
                    lean_dec(v_inst_3154_);
                    v___x_3172_ = lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3175_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3175_, 0, v_modifyEnv_3170_);
                lean_closure_set(v___f_3175_, 1, v___x_3174_);
                v___x_3176_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3176_, 0, lean_box(0));
                lean_closure_set(v___x_3176_, 1, lean_box(0));
                lean_closure_set(v___x_3176_, 2, lean_box(0));
                lean_closure_set(v___x_3176_, 3, lean_box(0));
                lean_closure_set(v___x_3176_, 4, v_getEnv_3169_);
                if v_isShared_3173_ == 0 {
                    lean_ctor_set(v___x_3172_, 1, v___f_3175_);
                    lean_ctor_set(v___x_3172_, 0, v___x_3176_);
                    v___x_3178_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3176_);
                    lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___f_3175_);
                    v___x_3178_ = v_reuseFailAlloc_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_toBind_3156_, 2);
                lean_inc_ref(v___x_3178_);
                lean_inc_ref_n(v___x_3155_, 3);
                v___f_3179_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed
                        as *mut core::ffi::c_void,
                    11,
                    7,
                );
                lean_closure_set(v___f_3179_, 0, v_inst_3153_);
                lean_closure_set(v___f_3179_, 1, v___x_3174_);
                lean_closure_set(v___f_3179_, 2, v___x_3155_);
                lean_closure_set(v___f_3179_, 3, v___x_3178_);
                lean_closure_set(v___f_3179_, 4, v_toBind_3156_);
                lean_closure_set(v___f_3179_, 5, v___f_3157_);
                lean_closure_set(v___f_3179_, 6, v___x_3158_);
                lean_inc_n(v___y_3167_, 2);
                v___f_3180_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                lean_closure_set(v___f_3180_, 0, v___x_3155_);
                lean_closure_set(v___f_3180_, 1, v___f_3179_);
                lean_closure_set(v___f_3180_, 2, v___x_3159_);
                lean_closure_set(v___f_3180_, 3, v___y_3167_);
                lean_closure_set(v___f_3180_, 4, v_toBind_3156_);
                lean_closure_set(v___f_3180_, 5, v___f_3160_);
                lean_inc_ref(v_inst_3161_);
                v___f_3181_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3181_, 0, v_inst_3161_);
                v___f_3182_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3182_, 0, v_inst_3161_);
                v___x_3183_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3183_, 0, v___f_3181_);
                lean_ctor_set(v___x_3183_, 1, v___f_3182_);
                v___x_3184_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3185_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3174_,
                    v___x_3184_,
                    v_inst_3162_,
                );
                v___f_3186_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3186_, 0, v_inst_3163_);
                lean_closure_set(v___f_3186_, 1, v___x_3174_);
                v___x_3187_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3186_,
                    v___x_3155_,
                );
                v___x_3188_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3188_, 0, v___x_3183_);
                lean_ctor_set(v___x_3188_, 1, v___x_3185_);
                lean_ctor_set(v___x_3188_, 2, v___x_3187_);
                v___x_7088__overap_3189_ = l_Lean_resolveNamespace___redArg(
                    v___x_3155_,
                    v___x_3168_,
                    v___x_3178_,
                    v___x_3188_,
                    v_a_3164_,
                );
                v___x_3190_ = lean_apply_1(v___x_7088__overap_3189_, v___y_3167_);
                v___x_3191_ = lean_apply_4(
                    v_toBind_3156_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_3194_: *mut LeanObject,
    mut v_inst_3195_: *mut LeanObject,
    mut v_inst_3196_: *mut LeanObject,
    mut v___x_3197_: *mut LeanObject,
    mut v_toBind_3198_: *mut LeanObject,
    mut v___f_3199_: *mut LeanObject,
    mut v___x_3200_: *mut LeanObject,
    mut v___x_3201_: *mut LeanObject,
    mut v___f_3202_: *mut LeanObject,
    mut v_inst_3203_: *mut LeanObject,
    mut v_inst_3204_: *mut LeanObject,
    mut v_inst_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
    mut v_x_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3210_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3209_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(
    mut v_toPure_3238_: *mut LeanObject,
    mut v_inst_3239_: *mut LeanObject,
    mut v_toBind_3240_: *mut LeanObject,
    mut v___x_3241_: u8,
    mut v___x_3242_: *mut LeanObject,
    mut v___x_3243_: *mut LeanObject,
    mut v___x_3244_: *mut LeanObject,
    mut v_stx_3245_: *mut LeanObject,
    mut v___f_3246_: *mut LeanObject,
    mut v_inst_3247_: *mut LeanObject,
    mut v_inst_3248_: *mut LeanObject,
    mut v_inst_3249_: *mut LeanObject,
    mut v___f_3250_: *mut LeanObject,
    mut v___f_3251_: *mut LeanObject,
    mut v_inst_3252_: *mut LeanObject,
    mut v_inst_3253_: *mut LeanObject,
    mut v___x_3254_: *mut LeanObject,
    mut v_inst_3255_: *mut LeanObject,
    mut v_inst_3256_: *mut LeanObject,
    mut v_inst_3257_: *mut LeanObject,
    mut v___f_3258_: *mut LeanObject,
    mut v_ref_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: u8 = 0;
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___f_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125__overap_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ns_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151__overap_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3303_: usize = 0;
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v_tos_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_froms_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179__overap_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___f_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ns_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223__overap_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___f_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ns_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7244__overap_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v___f_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nss_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3423_: usize = 0;
    let mut v___x_3424_: usize = 0;
    let mut v___x_7255__overap_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nss_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3437_: usize = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_7267__overap_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_toBind_3240_);
                lean_inc(v_inst_3239_);
                lean_inc(v_ref_3259_);
                lean_inc(v_toPure_3238_);
                v___f_3260_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3260_, 0, v_toPure_3238_);
                lean_closure_set(v___f_3260_, 1, v_ref_3259_);
                lean_closure_set(v___f_3260_, 2, v_inst_3239_);
                lean_closure_set(v___f_3260_, 3, v_toBind_3240_);
                if v___x_3241_ == 0 {
                    v___x_3261_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0;
                    lean_inc_ref(v___x_3244_);
                    lean_inc_ref(v___x_3243_);
                    lean_inc_ref(v___x_3242_);
                    v___x_3262_ =
                        l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3261_);
                    lean_inc(v_stx_3245_);
                    v___x_3263_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3262_);
                    lean_dec(v___x_3262_);
                    if v___x_3263_ == 0 {
                        v___x_3264_ =
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1;
                        lean_inc_ref(v___x_3244_);
                        lean_inc_ref(v___x_3243_);
                        lean_inc_ref(v___x_3242_);
                        v___x_3265_ =
                            l_Lean_Name_mkStr4(v___x_3242_, v___x_3243_, v___x_3244_, v___x_3264_);
                        lean_inc(v_stx_3245_);
                        v___x_3266_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3265_);
                        lean_dec(v___x_3265_);
                        if v___x_3266_ == 0 {
                            v___x_3267_ =
                                l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2;
                            lean_inc_ref(v___x_3244_);
                            lean_inc_ref(v___x_3243_);
                            lean_inc_ref(v___x_3242_);
                            v___x_3268_ = l_Lean_Name_mkStr4(
                                v___x_3242_,
                                v___x_3243_,
                                v___x_3244_,
                                v___x_3267_,
                            );
                            lean_inc(v_stx_3245_);
                            v___x_3269_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3268_);
                            lean_dec(v___x_3268_);
                            if v___x_3269_ == 0 {
                                lean_dec_ref(v___f_3258_);
                                v___x_3270_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3;
                                lean_inc_ref(v___x_3244_);
                                lean_inc_ref(v___x_3243_);
                                lean_inc_ref(v___x_3242_);
                                v___x_3271_ = l_Lean_Name_mkStr4(
                                    v___x_3242_,
                                    v___x_3243_,
                                    v___x_3244_,
                                    v___x_3270_,
                                );
                                lean_inc(v_stx_3245_);
                                v___x_3272_ = l_Lean_Syntax_isOfKind(v_stx_3245_, v___x_3271_);
                                lean_dec(v___x_3271_);
                                if v___x_3272_ == 0 {
                                    lean_dec(v_inst_3257_);
                                    lean_dec_ref(v_inst_3256_);
                                    lean_dec_ref(v_inst_3255_);
                                    lean_dec_ref(v___x_3254_);
                                    lean_dec(v_inst_3253_);
                                    lean_dec_ref(v_inst_3252_);
                                    lean_dec_ref(v___f_3251_);
                                    lean_dec_ref(v___f_3250_);
                                    lean_dec_ref(v_inst_3249_);
                                    lean_dec_ref(v_inst_3248_);
                                    lean_dec(v_stx_3245_);
                                    lean_dec_ref(v___x_3244_);
                                    lean_dec_ref(v___x_3243_);
                                    lean_dec_ref(v___x_3242_);
                                    lean_dec(v_inst_3239_);
                                    lean_dec(v_toPure_3238_);
                                    lean_inc(v_ref_3259_);
                                    v___f_3273_ = lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    lean_closure_set(v___f_3273_, 0, v___f_3246_);
                                    lean_closure_set(v___f_3273_, 1, v_ref_3259_);
                                    lean_inc_ref(v_inst_3247_);
                                    v___f_3274_ = lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        1,
                                    );
                                    lean_closure_set(v___f_3274_, 0, v_inst_3247_);
                                    v___f_3275_ = lean_alloc_closure(
                                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                                            as *mut core::ffi::c_void,
                                        5,
                                        1,
                                    );
                                    lean_closure_set(v___f_3275_, 0, v_inst_3247_);
                                    v___x_3276_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3276_, 0, v___f_3274_);
                                    lean_ctor_set(v___x_3276_, 1, v___f_3275_);
                                    v___x_7125__overap_3277_ =
                                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3276_);
                                    v___x_3278_ =
                                        lean_apply_1(v___x_7125__overap_3277_, v_ref_3259_);
                                    lean_inc(v_toBind_3240_);
                                    v___x_3279_ = lean_apply_4(
                                        v_toBind_3240_,
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_3278_,
                                        v___f_3273_,
                                    );
                                    v___x_3280_ = lean_apply_4(
                                        v_toBind_3240_,
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_3279_,
                                        v___f_3260_,
                                    );
                                    return v___x_3280_;
                                } else {
                                    lean_inc_n(v_ref_3259_, 2);
                                    lean_inc(v___f_3246_);
                                    v___f_3281_ = lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    lean_closure_set(v___f_3281_, 0, v___f_3246_);
                                    lean_closure_set(v___f_3281_, 1, v_ref_3259_);
                                    v___f_3282_ = lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    lean_closure_set(v___f_3282_, 0, v___f_3246_);
                                    lean_closure_set(v___f_3282_, 1, v_ref_3259_);
                                    v___x_3283_ = lean_unsigned_to_nat(0);
                                    v_ns_3284_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3283_);
                                    v___x_3285_ = lean_unsigned_to_nat(2);
                                    v___f_3286_ = lean_alloc_closure(
                                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed
                                            as *mut core::ffi::c_void,
                                        6,
                                        5,
                                    );
                                    lean_closure_set(v___f_3286_, 0, v___x_3242_);
                                    lean_closure_set(v___f_3286_, 1, v___x_3243_);
                                    lean_closure_set(v___f_3286_, 2, v___x_3244_);
                                    lean_closure_set(v___f_3286_, 3, v___x_3283_);
                                    lean_closure_set(v___f_3286_, 4, v___x_3285_);
                                    v___x_3287_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3285_);
                                    lean_dec(v_stx_3245_);
                                    v___x_3288_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13;
                                    v___x_3333_ = l_Lean_Syntax_getArgs(v___x_3287_);
                                    lean_dec(v___x_3287_);
                                    v___x_3334_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14;
                                    v___x_3335_ = lean_array_get_size(v___x_3333_);
                                    v___x_3336_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                                    v___x_3337_ = lean_nat_dec_lt(v___x_3283_, v___x_3335_);
                                    if v___x_3337_ == 0 {
                                        lean_dec_ref(v___x_3333_);
                                        v___y_3290_ = v___x_3334_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3338_ = lean_box((v___x_3272_) as usize);
                                        v___x_3339_ = lean_box((v___x_3269_) as usize);
                                        v___f_3340_ = lean_alloc_closure(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed as *mut core::ffi::c_void, 4, 2);
                                        lean_closure_set(v___f_3340_, 0, v___x_3338_);
                                        lean_closure_set(v___f_3340_, 1, v___x_3339_);
                                        v___x_3341_ = lean_box((v___x_3272_) as usize);
                                        v___x_3342_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_3342_, 0, v___x_3341_);
                                        lean_ctor_set(v___x_3342_, 1, v___x_3334_);
                                        v___x_3343_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
                                        if v___x_3343_ == 0 {
                                            if v___x_3337_ == 0 {
                                                lean_dec_ref_known(v___x_3342_, 2);
                                                lean_dec_ref(v___f_3340_);
                                                lean_dec_ref(v___x_3333_);
                                                v___y_3290_ = v___x_3334_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3344_ = 0usize;
                                                v___x_3345_ = lean_usize_of_nat(v___x_3335_);
                                                v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3344_, v___x_3345_, v___x_3342_);
                                                v_snd_3347_ = lean_ctor_get(v___x_3346_, 1);
                                                lean_inc(v_snd_3347_);
                                                lean_dec(v___x_3346_);
                                                v___y_3290_ = v_snd_3347_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___x_3348_ = 0usize;
                                            v___x_3349_ = lean_usize_of_nat(v___x_3335_);
                                            v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3336_, v___f_3340_, v___x_3333_, v___x_3348_, v___x_3349_, v___x_3342_);
                                            v_snd_3351_ = lean_ctor_get(v___x_3350_, 1);
                                            lean_inc(v_snd_3351_);
                                            lean_dec(v___x_3350_);
                                            v___y_3290_ = v_snd_3351_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___f_3251_);
                                lean_dec_ref(v___f_3250_);
                                lean_dec_ref(v___x_3244_);
                                lean_dec_ref(v___x_3243_);
                                lean_dec_ref(v___x_3242_);
                                lean_inc(v_inst_3239_);
                                v___x_3352_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                    v_inst_3248_,
                                    v_inst_3239_,
                                );
                                v_getEnv_3353_ = lean_ctor_get(v_inst_3249_, 0);
                                v_modifyEnv_3354_ = lean_ctor_get(v_inst_3249_, 1);
                                v_isSharedCheck_3383_ = (!lean_is_exclusive(v_inst_3249_)) as u8;
                                if v_isSharedCheck_3383_ == 0 {
                                    v___x_3356_ = v_inst_3249_;
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_modifyEnv_3354_);
                                    lean_inc(v_getEnv_3353_);
                                    lean_dec(v_inst_3249_);
                                    v___x_3356_ = lean_box(0);
                                    v_isShared_3357_ = v_isSharedCheck_3383_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___f_3258_);
                            lean_dec_ref(v___f_3251_);
                            lean_dec_ref(v___f_3250_);
                            lean_dec_ref(v___x_3244_);
                            lean_dec_ref(v___x_3243_);
                            lean_dec_ref(v___x_3242_);
                            lean_inc(v_inst_3239_);
                            v___x_3384_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                                v_inst_3248_,
                                v_inst_3239_,
                            );
                            v_getEnv_3385_ = lean_ctor_get(v_inst_3249_, 0);
                            v_modifyEnv_3386_ = lean_ctor_get(v_inst_3249_, 1);
                            v_isSharedCheck_3415_ = (!lean_is_exclusive(v_inst_3249_)) as u8;
                            if v_isSharedCheck_3415_ == 0 {
                                v___x_3388_ = v_inst_3249_;
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_modifyEnv_3386_);
                                lean_inc(v_getEnv_3385_);
                                lean_dec(v_inst_3249_);
                                v___x_3388_ = lean_box(0);
                                v_isShared_3389_ = v_isSharedCheck_3415_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___f_3258_);
                        lean_dec(v_inst_3257_);
                        lean_dec_ref(v_inst_3256_);
                        lean_dec_ref(v_inst_3255_);
                        lean_dec_ref(v___f_3251_);
                        lean_dec_ref(v___f_3250_);
                        lean_dec_ref(v___x_3244_);
                        lean_dec_ref(v___x_3243_);
                        lean_dec_ref(v___x_3242_);
                        lean_inc(v_ref_3259_);
                        v___f_3416_ = lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3416_, 0, v___f_3246_);
                        lean_closure_set(v___f_3416_, 1, v_ref_3259_);
                        v___x_3417_ = lean_unsigned_to_nat(1);
                        v___x_3418_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3417_);
                        lean_dec(v_stx_3245_);
                        v_nss_3419_ = l_Lean_Syntax_getArgs(v___x_3418_);
                        lean_dec(v___x_3418_);
                        v___x_3420_ = lean_box(0);
                        v___f_3421_ = lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3421_, 0, v___x_3420_);
                        lean_closure_set(v___f_3421_, 1, v_toPure_3238_);
                        lean_inc_ref(v___f_3421_);
                        lean_inc_n(v_toBind_3240_, 2);
                        lean_inc_ref(v___x_3254_);
                        v___f_3422_ = lean_alloc_closure(
                            l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed
                                as *mut core::ffi::c_void,
                            15,
                            11,
                        );
                        lean_closure_set(v___f_3422_, 0, v_inst_3248_);
                        lean_closure_set(v___f_3422_, 1, v_inst_3239_);
                        lean_closure_set(v___f_3422_, 2, v_inst_3249_);
                        lean_closure_set(v___f_3422_, 3, v___x_3254_);
                        lean_closure_set(v___f_3422_, 4, v_toBind_3240_);
                        lean_closure_set(v___f_3422_, 5, v___f_3421_);
                        lean_closure_set(v___f_3422_, 6, v___x_3420_);
                        lean_closure_set(v___f_3422_, 7, v___f_3421_);
                        lean_closure_set(v___f_3422_, 8, v_inst_3247_);
                        lean_closure_set(v___f_3422_, 9, v_inst_3252_);
                        lean_closure_set(v___f_3422_, 10, v_inst_3253_);
                        v_sz_3423_ = lean_array_size(v_nss_3419_);
                        v___x_3424_ = 0usize;
                        v___x_7255__overap_3425_ =
                            l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_3254_,
                                v_nss_3419_,
                                v___f_3422_,
                                v_sz_3423_,
                                v___x_3424_,
                                v___x_3420_,
                            );
                        v___x_3426_ = lean_apply_1(v___x_7255__overap_3425_, v_ref_3259_);
                        v___x_3427_ = lean_apply_4(
                            v_toBind_3240_,
                            lean_box(0),
                            lean_box(0),
                            v___x_3426_,
                            v___f_3416_,
                        );
                        v___x_3428_ = lean_apply_4(
                            v_toBind_3240_,
                            lean_box(0),
                            lean_box(0),
                            v___x_3427_,
                            v___f_3260_,
                        );
                        return v___x_3428_;
                    }
                } else {
                    lean_dec_ref(v___f_3258_);
                    lean_dec(v_inst_3257_);
                    lean_dec_ref(v_inst_3256_);
                    lean_dec_ref(v_inst_3255_);
                    lean_dec_ref(v___f_3251_);
                    lean_dec_ref(v___f_3250_);
                    lean_dec_ref(v___x_3244_);
                    lean_dec_ref(v___x_3243_);
                    lean_dec_ref(v___x_3242_);
                    lean_inc(v_ref_3259_);
                    v___f_3429_ = lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_3429_, 0, v___f_3246_);
                    lean_closure_set(v___f_3429_, 1, v_ref_3259_);
                    v___x_3430_ = lean_unsigned_to_nat(0);
                    v___x_3431_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3430_);
                    lean_dec(v_stx_3245_);
                    v___x_3432_ = lean_box(0);
                    v_nss_3433_ = l_Lean_Syntax_getArgs(v___x_3431_);
                    lean_dec(v___x_3431_);
                    v___x_3434_ = lean_box(0);
                    v___f_3435_ = lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_3435_, 0, v___x_3434_);
                    lean_closure_set(v___f_3435_, 1, v_toPure_3238_);
                    lean_inc_ref(v___f_3435_);
                    lean_inc_n(v_toBind_3240_, 2);
                    lean_inc_ref(v___x_3254_);
                    v___f_3436_ = lean_alloc_closure(
                        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed
                            as *mut core::ffi::c_void,
                        16,
                        12,
                    );
                    lean_closure_set(v___f_3436_, 0, v_inst_3248_);
                    lean_closure_set(v___f_3436_, 1, v_inst_3239_);
                    lean_closure_set(v___f_3436_, 2, v_inst_3249_);
                    lean_closure_set(v___f_3436_, 3, v___x_3254_);
                    lean_closure_set(v___f_3436_, 4, v_toBind_3240_);
                    lean_closure_set(v___f_3436_, 5, v___f_3435_);
                    lean_closure_set(v___f_3436_, 6, v___x_3432_);
                    lean_closure_set(v___f_3436_, 7, v___x_3434_);
                    lean_closure_set(v___f_3436_, 8, v___f_3435_);
                    lean_closure_set(v___f_3436_, 9, v_inst_3247_);
                    lean_closure_set(v___f_3436_, 10, v_inst_3252_);
                    lean_closure_set(v___f_3436_, 11, v_inst_3253_);
                    v_sz_3437_ = lean_array_size(v_nss_3433_);
                    v___x_3438_ = 0usize;
                    v___x_7267__overap_3439_ =
                        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_3254_,
                            v_nss_3433_,
                            v___f_3436_,
                            v_sz_3437_,
                            v___x_3438_,
                            v___x_3434_,
                        );
                    v___x_3440_ = lean_apply_1(v___x_7267__overap_3439_, v_ref_3259_);
                    v___x_3441_ = lean_apply_4(
                        v_toBind_3240_,
                        lean_box(0),
                        lean_box(0),
                        v___x_3440_,
                        v___f_3429_,
                    );
                    v___x_3442_ = lean_apply_4(
                        v_toBind_3240_,
                        lean_box(0),
                        lean_box(0),
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
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_3288_,
                    v___f_3286_,
                    v_sz_3291_,
                    v___x_3292_,
                    v___y_3290_,
                );
                if lean_obj_tag(v___x_3293_) == 0 {
                    lean_dec(v_ns_3284_);
                    lean_dec_ref(v___f_3281_);
                    lean_dec(v_inst_3257_);
                    lean_dec_ref(v_inst_3256_);
                    lean_dec_ref(v_inst_3255_);
                    lean_dec_ref(v___x_3254_);
                    lean_dec(v_inst_3253_);
                    lean_dec_ref(v_inst_3252_);
                    lean_dec_ref(v___f_3251_);
                    lean_dec_ref(v___f_3250_);
                    lean_dec_ref(v_inst_3249_);
                    lean_dec_ref(v_inst_3248_);
                    lean_dec(v_inst_3239_);
                    lean_dec(v_toPure_3238_);
                    lean_inc_ref(v_inst_3247_);
                    v___f_3294_ = lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    lean_closure_set(v___f_3294_, 0, v_inst_3247_);
                    v___f_3295_ = lean_alloc_closure(
                        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    lean_closure_set(v___f_3295_, 0, v_inst_3247_);
                    v___x_3296_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3296_, 0, v___f_3294_);
                    lean_ctor_set(v___x_3296_, 1, v___f_3295_);
                    v___x_7151__overap_3297_ =
                        l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_3296_);
                    v___x_3298_ = lean_apply_1(v___x_7151__overap_3297_, v_ref_3259_);
                    lean_inc(v_toBind_3240_);
                    v___x_3299_ = lean_apply_4(
                        v_toBind_3240_,
                        lean_box(0),
                        lean_box(0),
                        v___x_3298_,
                        v___f_3282_,
                    );
                    v___x_3300_ = lean_apply_4(
                        v_toBind_3240_,
                        lean_box(0),
                        lean_box(0),
                        v___x_3299_,
                        v___f_3260_,
                    );
                    return v___x_3300_;
                } else {
                    lean_dec_ref(v___f_3282_);
                    v_val_3301_ = lean_ctor_get(v___x_3293_, 0);
                    lean_inc(v_val_3301_);
                    lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3302_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9;
                    v_sz_3303_ = lean_array_size(v_val_3301_);
                    lean_inc(v_inst_3239_);
                    v___x_3304_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(
                        v_inst_3248_,
                        v_inst_3239_,
                    );
                    v_getEnv_3305_ = lean_ctor_get(v_inst_3249_, 0);
                    v_modifyEnv_3306_ = lean_ctor_get(v_inst_3249_, 1);
                    v_isSharedCheck_3332_ = (!lean_is_exclusive(v_inst_3249_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3308_ = v_inst_3249_;
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_modifyEnv_3306_);
                        lean_inc(v_getEnv_3305_);
                        lean_dec(v_inst_3249_);
                        v___x_3308_ = lean_box(0);
                        v_isShared_3309_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_3301_);
                v_tos_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_3302_,
                    v___f_3250_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v_froms_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_3302_,
                    v___f_3251_,
                    v_sz_3303_,
                    v___x_3292_,
                    v_val_3301_,
                );
                v___x_3312_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3313_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3313_, 0, v_modifyEnv_3306_);
                lean_closure_set(v___f_3313_, 1, v___x_3312_);
                v___x_3314_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3314_, 0, lean_box(0));
                lean_closure_set(v___x_3314_, 1, lean_box(0));
                lean_closure_set(v___x_3314_, 2, lean_box(0));
                lean_closure_set(v___x_3314_, 3, lean_box(0));
                lean_closure_set(v___x_3314_, 4, v_getEnv_3305_);
                if v_isShared_3309_ == 0 {
                    lean_ctor_set(v___x_3308_, 1, v___f_3313_);
                    lean_ctor_set(v___x_3308_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3308_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3314_);
                    lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___f_3313_);
                    v___x_3316_ = v_reuseFailAlloc_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_inst_3247_);
                v___f_3317_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3317_, 0, v_inst_3247_);
                v___f_3318_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3318_, 0, v_inst_3247_);
                v___x_3319_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3319_, 0, v___f_3317_);
                lean_ctor_set(v___x_3319_, 1, v___f_3318_);
                v___x_3320_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3321_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3312_,
                    v___x_3320_,
                    v_inst_3252_,
                );
                v___f_3322_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3322_, 0, v_inst_3253_);
                lean_closure_set(v___f_3322_, 1, v___x_3312_);
                lean_inc_ref_n(v___x_3254_, 2);
                lean_inc_ref(v___f_3322_);
                v___x_3323_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3322_,
                    v___x_3254_,
                );
                lean_inc(v___x_3323_);
                lean_inc_ref(v___x_3321_);
                lean_inc_ref(v___x_3319_);
                v___x_3324_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3324_, 0, v___x_3319_);
                lean_ctor_set(v___x_3324_, 1, v___x_3321_);
                lean_ctor_set(v___x_3324_, 2, v___x_3323_);
                v___x_3325_ =
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1;
                lean_inc(v_ref_3259_);
                lean_inc_ref(v___x_3304_);
                lean_inc_ref(v___x_3324_);
                lean_inc_ref(v___x_3316_);
                lean_inc_n(v_toBind_3240_, 2);
                v___f_3326_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed
                        as *mut core::ffi::c_void,
                    21,
                    20,
                );
                lean_closure_set(v___f_3326_, 0, v_froms_3311_);
                lean_closure_set(v___f_3326_, 1, v_tos_3310_);
                lean_closure_set(v___f_3326_, 2, v_toPure_3238_);
                lean_closure_set(v___f_3326_, 3, v___x_3312_);
                lean_closure_set(v___f_3326_, 4, v_inst_3255_);
                lean_closure_set(v___f_3326_, 5, v_inst_3239_);
                lean_closure_set(v___f_3326_, 6, v_toBind_3240_);
                lean_closure_set(v___f_3326_, 7, v___x_3254_);
                lean_closure_set(v___f_3326_, 8, v___x_3316_);
                lean_closure_set(v___f_3326_, 9, v___x_3324_);
                lean_closure_set(v___f_3326_, 10, v_inst_3256_);
                lean_closure_set(v___f_3326_, 11, v_inst_3257_);
                lean_closure_set(v___f_3326_, 12, v___x_3319_);
                lean_closure_set(v___f_3326_, 13, v___x_3321_);
                lean_closure_set(v___f_3326_, 14, v___x_3323_);
                lean_closure_set(v___f_3326_, 15, v___f_3322_);
                lean_closure_set(v___f_3326_, 16, v___x_3304_);
                lean_closure_set(v___f_3326_, 17, v___x_3325_);
                lean_closure_set(v___f_3326_, 18, v_ref_3259_);
                lean_closure_set(v___f_3326_, 19, v___f_3281_);
                v___x_7179__overap_3327_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3304_,
                    v___x_3316_,
                    v___x_3324_,
                    v_ns_3284_,
                );
                v___x_3328_ = lean_apply_1(v___x_7179__overap_3327_, v_ref_3259_);
                v___x_3329_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3328_,
                    v___f_3326_,
                );
                v___x_3330_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3329_,
                    v___f_3260_,
                );
                return v___x_3330_;
            }
            4 => {
                lean_inc(v_ref_3259_);
                v___f_3358_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3358_, 0, v___f_3246_);
                lean_closure_set(v___f_3358_, 1, v_ref_3259_);
                v___x_3359_ = lean_unsigned_to_nat(0);
                v_ns_3360_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3359_);
                v___x_3361_ = lean_unsigned_to_nat(2);
                v___x_3362_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3361_);
                lean_dec(v_stx_3245_);
                v_ids_3363_ = l_Lean_Syntax_getArgs(v___x_3362_);
                lean_dec(v___x_3362_);
                v___x_3364_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3365_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3365_, 0, v_modifyEnv_3354_);
                lean_closure_set(v___f_3365_, 1, v___x_3364_);
                v___x_3366_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3366_, 0, lean_box(0));
                lean_closure_set(v___x_3366_, 1, lean_box(0));
                lean_closure_set(v___x_3366_, 2, lean_box(0));
                lean_closure_set(v___x_3366_, 3, lean_box(0));
                lean_closure_set(v___x_3366_, 4, v_getEnv_3353_);
                if v_isShared_3357_ == 0 {
                    lean_ctor_set(v___x_3356_, 1, v___f_3365_);
                    lean_ctor_set(v___x_3356_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3356_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3366_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___f_3365_);
                    v___x_3368_ = v_reuseFailAlloc_3382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v_inst_3247_);
                v___f_3369_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3369_, 0, v_inst_3247_);
                v___f_3370_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3370_, 0, v_inst_3247_);
                v___x_3371_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3371_, 0, v___f_3369_);
                lean_ctor_set(v___x_3371_, 1, v___f_3370_);
                v___x_3372_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3373_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3364_,
                    v___x_3372_,
                    v_inst_3252_,
                );
                v___f_3374_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3374_, 0, v_inst_3253_);
                lean_closure_set(v___f_3374_, 1, v___x_3364_);
                lean_inc_ref_n(v___x_3254_, 2);
                lean_inc_ref(v___f_3374_);
                v___x_3375_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3374_,
                    v___x_3254_,
                );
                lean_inc(v___x_3375_);
                lean_inc_ref(v___x_3373_);
                lean_inc_ref(v___x_3371_);
                v___x_3376_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3376_, 0, v___x_3371_);
                lean_ctor_set(v___x_3376_, 1, v___x_3373_);
                lean_ctor_set(v___x_3376_, 2, v___x_3375_);
                lean_inc_ref(v___x_3352_);
                lean_inc_ref(v___x_3376_);
                lean_inc_ref(v___x_3368_);
                lean_inc_n(v_toBind_3240_, 2);
                lean_inc(v_ref_3259_);
                v___f_3377_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed
                        as *mut core::ffi::c_void,
                    20,
                    19,
                );
                lean_closure_set(v___f_3377_, 0, v_ids_3363_);
                lean_closure_set(v___f_3377_, 1, v___f_3258_);
                lean_closure_set(v___f_3377_, 2, v_inst_3239_);
                lean_closure_set(v___f_3377_, 3, v_ref_3259_);
                lean_closure_set(v___f_3377_, 4, v_toBind_3240_);
                lean_closure_set(v___f_3377_, 5, v___f_3358_);
                lean_closure_set(v___f_3377_, 6, v_toPure_3238_);
                lean_closure_set(v___f_3377_, 7, v___x_3364_);
                lean_closure_set(v___f_3377_, 8, v_inst_3255_);
                lean_closure_set(v___f_3377_, 9, v___x_3254_);
                lean_closure_set(v___f_3377_, 10, v___x_3368_);
                lean_closure_set(v___f_3377_, 11, v___x_3376_);
                lean_closure_set(v___f_3377_, 12, v_inst_3256_);
                lean_closure_set(v___f_3377_, 13, v_inst_3257_);
                lean_closure_set(v___f_3377_, 14, v___x_3371_);
                lean_closure_set(v___f_3377_, 15, v___x_3373_);
                lean_closure_set(v___f_3377_, 16, v___x_3375_);
                lean_closure_set(v___f_3377_, 17, v___f_3374_);
                lean_closure_set(v___f_3377_, 18, v___x_3352_);
                v___x_7223__overap_3378_ = l_Lean_resolveUniqueNamespace___redArg(
                    v___x_3254_,
                    v___x_3352_,
                    v___x_3368_,
                    v___x_3376_,
                    v_ns_3360_,
                );
                v___x_3379_ = lean_apply_1(v___x_7223__overap_3378_, v_ref_3259_);
                v___x_3380_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3379_,
                    v___f_3377_,
                );
                v___x_3381_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3380_,
                    v___f_3260_,
                );
                return v___x_3381_;
            }
            6 => {
                lean_inc(v_ref_3259_);
                v___f_3390_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3390_, 0, v___f_3246_);
                lean_closure_set(v___f_3390_, 1, v_ref_3259_);
                v___x_3391_ = lean_unsigned_to_nat(0);
                v_ns_3392_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3391_);
                v___x_3393_ = lean_unsigned_to_nat(2);
                v___x_3394_ = l_Lean_Syntax_getArg(v_stx_3245_, v___x_3393_);
                lean_dec(v_stx_3245_);
                v_ids_3395_ = l_Lean_Syntax_getArgs(v___x_3394_);
                lean_dec(v___x_3394_);
                v___x_3396_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3397_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3397_, 0, v_modifyEnv_3386_);
                lean_closure_set(v___f_3397_, 1, v___x_3396_);
                v___x_3398_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3398_, 0, lean_box(0));
                lean_closure_set(v___x_3398_, 1, lean_box(0));
                lean_closure_set(v___x_3398_, 2, lean_box(0));
                lean_closure_set(v___x_3398_, 3, lean_box(0));
                lean_closure_set(v___x_3398_, 4, v_getEnv_3385_);
                if v_isShared_3389_ == 0 {
                    lean_ctor_set(v___x_3388_, 1, v___f_3397_);
                    lean_ctor_set(v___x_3388_, 0, v___x_3398_);
                    v___x_3400_ = v___x_3388_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3398_);
                    lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___f_3397_);
                    v___x_3400_ = v_reuseFailAlloc_3414_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc_ref(v_inst_3247_);
                v___f_3401_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3401_, 0, v_inst_3247_);
                v___f_3402_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3402_, 0, v_inst_3247_);
                v___x_3403_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3403_, 0, v___f_3401_);
                lean_ctor_set(v___x_3403_, 1, v___f_3402_);
                v___x_3404_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1;
                v___x_3405_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v___x_3396_,
                    v___x_3404_,
                    v_inst_3252_,
                );
                v___f_3406_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3406_, 0, v_inst_3253_);
                lean_closure_set(v___f_3406_, 1, v___x_3396_);
                lean_inc_ref_n(v___x_3254_, 2);
                lean_inc_ref(v___f_3406_);
                v___x_3407_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3406_,
                    v___x_3254_,
                );
                lean_inc(v___x_3407_);
                lean_inc_ref(v___x_3405_);
                lean_inc_ref(v___x_3403_);
                v___x_3408_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3408_, 0, v___x_3403_);
                lean_ctor_set(v___x_3408_, 1, v___x_3405_);
                lean_ctor_set(v___x_3408_, 2, v___x_3407_);
                lean_inc(v_ref_3259_);
                lean_inc_ref(v___x_3384_);
                lean_inc_ref(v___x_3408_);
                lean_inc_ref(v___x_3400_);
                lean_inc_n(v_toBind_3240_, 2);
                v___f_3409_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed
                        as *mut core::ffi::c_void,
                    19,
                    18,
                );
                lean_closure_set(v___f_3409_, 0, v_toPure_3238_);
                lean_closure_set(v___f_3409_, 1, v___x_3396_);
                lean_closure_set(v___f_3409_, 2, v_inst_3255_);
                lean_closure_set(v___f_3409_, 3, v_inst_3239_);
                lean_closure_set(v___f_3409_, 4, v_toBind_3240_);
                lean_closure_set(v___f_3409_, 5, v___x_3254_);
                lean_closure_set(v___f_3409_, 6, v___x_3400_);
                lean_closure_set(v___f_3409_, 7, v___x_3408_);
                lean_closure_set(v___f_3409_, 8, v_inst_3256_);
                lean_closure_set(v___f_3409_, 9, v_inst_3257_);
                lean_closure_set(v___f_3409_, 10, v___x_3403_);
                lean_closure_set(v___f_3409_, 11, v___x_3405_);
                lean_closure_set(v___f_3409_, 12, v___x_3407_);
                lean_closure_set(v___f_3409_, 13, v___f_3406_);
                lean_closure_set(v___f_3409_, 14, v___x_3384_);
                lean_closure_set(v___f_3409_, 15, v_ids_3395_);
                lean_closure_set(v___f_3409_, 16, v_ref_3259_);
                lean_closure_set(v___f_3409_, 17, v___f_3390_);
                v___x_7244__overap_3410_ = l_Lean_resolveNamespace___redArg(
                    v___x_3254_,
                    v___x_3384_,
                    v___x_3400_,
                    v___x_3408_,
                    v_ns_3392_,
                );
                v___x_3411_ = lean_apply_1(v___x_7244__overap_3410_, v_ref_3259_);
                v___x_3412_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3411_,
                    v___f_3409_,
                );
                v___x_3413_ = lean_apply_4(
                    v_toBind_3240_,
                    lean_box(0),
                    lean_box(0),
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3443_: *mut LeanObject = *_args.add(0);
    let mut v_inst_3444_: *mut LeanObject = *_args.add(1);
    let mut v_toBind_3445_: *mut LeanObject = *_args.add(2);
    let mut v___x_3446_: *mut LeanObject = *_args.add(3);
    let mut v___x_3447_: *mut LeanObject = *_args.add(4);
    let mut v___x_3448_: *mut LeanObject = *_args.add(5);
    let mut v___x_3449_: *mut LeanObject = *_args.add(6);
    let mut v_stx_3450_: *mut LeanObject = *_args.add(7);
    let mut v___f_3451_: *mut LeanObject = *_args.add(8);
    let mut v_inst_3452_: *mut LeanObject = *_args.add(9);
    let mut v_inst_3453_: *mut LeanObject = *_args.add(10);
    let mut v_inst_3454_: *mut LeanObject = *_args.add(11);
    let mut v___f_3455_: *mut LeanObject = *_args.add(12);
    let mut v___f_3456_: *mut LeanObject = *_args.add(13);
    let mut v_inst_3457_: *mut LeanObject = *_args.add(14);
    let mut v_inst_3458_: *mut LeanObject = *_args.add(15);
    let mut v___x_3459_: *mut LeanObject = *_args.add(16);
    let mut v_inst_3460_: *mut LeanObject = *_args.add(17);
    let mut v_inst_3461_: *mut LeanObject = *_args.add(18);
    let mut v_inst_3462_: *mut LeanObject = *_args.add(19);
    let mut v___f_3463_: *mut LeanObject = *_args.add(20);
    let mut v_ref_3464_: *mut LeanObject = *_args.add(21);
    let mut v___x_8610__boxed_3465_: u8 = 0;
    let mut v_res_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_8610__boxed_3465_ = (lean_unbox(v___x_3446_) as u8);
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
    mut v_toPure_3467_: *mut LeanObject,
    mut v_____x_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3469_ = lean_ctor_get(v_____x_3468_, 0);
    lean_inc(v_fst_3469_);
    lean_dec_ref(v_____x_3468_);
    v___x_3470_ = lean_apply_2(v_toPure_3467_, lean_box(0), v_fst_3469_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(
    mut v_toApplicative_3480_: *mut LeanObject,
    mut v_stx_3481_: *mut LeanObject,
    mut v_____do__lift_3482_: *mut LeanObject,
    mut v_inst_3483_: *mut LeanObject,
    mut v_toBind_3484_: *mut LeanObject,
    mut v___f_3485_: *mut LeanObject,
    mut v_inst_3486_: *mut LeanObject,
    mut v_inst_3487_: *mut LeanObject,
    mut v_inst_3488_: *mut LeanObject,
    mut v___f_3489_: *mut LeanObject,
    mut v___f_3490_: *mut LeanObject,
    mut v_inst_3491_: *mut LeanObject,
    mut v_inst_3492_: *mut LeanObject,
    mut v___x_3493_: *mut LeanObject,
    mut v_inst_3494_: *mut LeanObject,
    mut v_inst_3495_: *mut LeanObject,
    mut v_inst_3496_: *mut LeanObject,
    mut v___f_3497_: *mut LeanObject,
    mut v_____do__lift_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_3499_ = lean_ctor_get(v_toApplicative_3480_, 1);
    lean_inc_n(v_toPure_3499_, 2);
    lean_dec_ref(v_toApplicative_3480_);
    v___x_3500_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0;
    v___x_3501_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1;
    v___x_3502_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2;
    v___x_3503_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4;
    lean_inc(v_stx_3481_);
    v___x_3504_ = l_Lean_Syntax_isOfKind(v_stx_3481_, v___x_3503_);
    v___x_3505_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3505_, 0, v_____do__lift_3482_);
    lean_ctor_set(v___x_3505_, 1, v_____do__lift_3498_);
    v___x_3506_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_3506_, 0, lean_box(0));
    lean_closure_set(v___x_3506_, 1, lean_box(0));
    lean_closure_set(v___x_3506_, 2, v___x_3505_);
    lean_inc(v_inst_3483_);
    v___x_3507_ = lean_apply_2(v_inst_3483_, lean_box(0), v___x_3506_);
    v___x_3508_ = lean_box((v___x_3504_) as usize);
    lean_inc_n(v_toBind_3484_, 2);
    v___f_3509_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed as *mut core::ffi::c_void,
        22,
        21,
    );
    lean_closure_set(v___f_3509_, 0, v_toPure_3499_);
    lean_closure_set(v___f_3509_, 1, v_inst_3483_);
    lean_closure_set(v___f_3509_, 2, v_toBind_3484_);
    lean_closure_set(v___f_3509_, 3, v___x_3508_);
    lean_closure_set(v___f_3509_, 4, v___x_3500_);
    lean_closure_set(v___f_3509_, 5, v___x_3501_);
    lean_closure_set(v___f_3509_, 6, v___x_3502_);
    lean_closure_set(v___f_3509_, 7, v_stx_3481_);
    lean_closure_set(v___f_3509_, 8, v___f_3485_);
    lean_closure_set(v___f_3509_, 9, v_inst_3486_);
    lean_closure_set(v___f_3509_, 10, v_inst_3487_);
    lean_closure_set(v___f_3509_, 11, v_inst_3488_);
    lean_closure_set(v___f_3509_, 12, v___f_3489_);
    lean_closure_set(v___f_3509_, 13, v___f_3490_);
    lean_closure_set(v___f_3509_, 14, v_inst_3491_);
    lean_closure_set(v___f_3509_, 15, v_inst_3492_);
    lean_closure_set(v___f_3509_, 16, v___x_3493_);
    lean_closure_set(v___f_3509_, 17, v_inst_3494_);
    lean_closure_set(v___f_3509_, 18, v_inst_3495_);
    lean_closure_set(v___f_3509_, 19, v_inst_3496_);
    lean_closure_set(v___f_3509_, 20, v___f_3497_);
    v___f_3510_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3510_, 0, v_toPure_3499_);
    v___x_3511_ = lean_apply_4(
        v_toBind_3484_,
        lean_box(0),
        lean_box(0),
        v___x_3507_,
        v___f_3509_,
    );
    v___x_3512_ = lean_apply_4(
        v_toBind_3484_,
        lean_box(0),
        lean_box(0),
        v___x_3511_,
        v___f_3510_,
    );
    return v___x_3512_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3513_: *mut LeanObject = *_args.add(0);
    let mut v_stx_3514_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_3515_: *mut LeanObject = *_args.add(2);
    let mut v_inst_3516_: *mut LeanObject = *_args.add(3);
    let mut v_toBind_3517_: *mut LeanObject = *_args.add(4);
    let mut v___f_3518_: *mut LeanObject = *_args.add(5);
    let mut v_inst_3519_: *mut LeanObject = *_args.add(6);
    let mut v_inst_3520_: *mut LeanObject = *_args.add(7);
    let mut v_inst_3521_: *mut LeanObject = *_args.add(8);
    let mut v___f_3522_: *mut LeanObject = *_args.add(9);
    let mut v___f_3523_: *mut LeanObject = *_args.add(10);
    let mut v_inst_3524_: *mut LeanObject = *_args.add(11);
    let mut v_inst_3525_: *mut LeanObject = *_args.add(12);
    let mut v___x_3526_: *mut LeanObject = *_args.add(13);
    let mut v_inst_3527_: *mut LeanObject = *_args.add(14);
    let mut v_inst_3528_: *mut LeanObject = *_args.add(15);
    let mut v_inst_3529_: *mut LeanObject = *_args.add(16);
    let mut v___f_3530_: *mut LeanObject = *_args.add(17);
    let mut v_____do__lift_3531_: *mut LeanObject = *_args.add(18);
    let mut v_res_3532_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_3533_: *mut LeanObject,
    mut v_stx_3534_: *mut LeanObject,
    mut v_inst_3535_: *mut LeanObject,
    mut v_toBind_3536_: *mut LeanObject,
    mut v___f_3537_: *mut LeanObject,
    mut v_inst_3538_: *mut LeanObject,
    mut v_inst_3539_: *mut LeanObject,
    mut v_inst_3540_: *mut LeanObject,
    mut v___f_3541_: *mut LeanObject,
    mut v___f_3542_: *mut LeanObject,
    mut v_inst_3543_: *mut LeanObject,
    mut v_inst_3544_: *mut LeanObject,
    mut v___x_3545_: *mut LeanObject,
    mut v_inst_3546_: *mut LeanObject,
    mut v_inst_3547_: *mut LeanObject,
    mut v_inst_3548_: *mut LeanObject,
    mut v___f_3549_: *mut LeanObject,
    mut v_getCurrNamespace_3550_: *mut LeanObject,
    mut v_____do__lift_3551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_3536_);
    v___f_3552_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    lean_closure_set(v___f_3552_, 0, v_toApplicative_3533_);
    lean_closure_set(v___f_3552_, 1, v_stx_3534_);
    lean_closure_set(v___f_3552_, 2, v_____do__lift_3551_);
    lean_closure_set(v___f_3552_, 3, v_inst_3535_);
    lean_closure_set(v___f_3552_, 4, v_toBind_3536_);
    lean_closure_set(v___f_3552_, 5, v___f_3537_);
    lean_closure_set(v___f_3552_, 6, v_inst_3538_);
    lean_closure_set(v___f_3552_, 7, v_inst_3539_);
    lean_closure_set(v___f_3552_, 8, v_inst_3540_);
    lean_closure_set(v___f_3552_, 9, v___f_3541_);
    lean_closure_set(v___f_3552_, 10, v___f_3542_);
    lean_closure_set(v___f_3552_, 11, v_inst_3543_);
    lean_closure_set(v___f_3552_, 12, v_inst_3544_);
    lean_closure_set(v___f_3552_, 13, v___x_3545_);
    lean_closure_set(v___f_3552_, 14, v_inst_3546_);
    lean_closure_set(v___f_3552_, 15, v_inst_3547_);
    lean_closure_set(v___f_3552_, 16, v_inst_3548_);
    lean_closure_set(v___f_3552_, 17, v___f_3549_);
    v___x_3553_ = lean_apply_4(
        v_toBind_3536_,
        lean_box(0),
        lean_box(0),
        v_getCurrNamespace_3550_,
        v___f_3552_,
    );
    return v___x_3553_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3554_: *mut LeanObject = *_args.add(0);
    let mut v_stx_3555_: *mut LeanObject = *_args.add(1);
    let mut v_inst_3556_: *mut LeanObject = *_args.add(2);
    let mut v_toBind_3557_: *mut LeanObject = *_args.add(3);
    let mut v___f_3558_: *mut LeanObject = *_args.add(4);
    let mut v_inst_3559_: *mut LeanObject = *_args.add(5);
    let mut v_inst_3560_: *mut LeanObject = *_args.add(6);
    let mut v_inst_3561_: *mut LeanObject = *_args.add(7);
    let mut v___f_3562_: *mut LeanObject = *_args.add(8);
    let mut v___f_3563_: *mut LeanObject = *_args.add(9);
    let mut v_inst_3564_: *mut LeanObject = *_args.add(10);
    let mut v_inst_3565_: *mut LeanObject = *_args.add(11);
    let mut v___x_3566_: *mut LeanObject = *_args.add(12);
    let mut v_inst_3567_: *mut LeanObject = *_args.add(13);
    let mut v_inst_3568_: *mut LeanObject = *_args.add(14);
    let mut v_inst_3569_: *mut LeanObject = *_args.add(15);
    let mut v___f_3570_: *mut LeanObject = *_args.add(16);
    let mut v_getCurrNamespace_3571_: *mut LeanObject = *_args.add(17);
    let mut v_____do__lift_3572_: *mut LeanObject = *_args.add(18);
    let mut v_res_3573_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_3577_: *mut LeanObject,
    mut v_inst_3578_: *mut LeanObject,
    mut v_inst_3579_: *mut LeanObject,
    mut v_inst_3580_: *mut LeanObject,
    mut v_inst_3581_: *mut LeanObject,
    mut v_inst_3582_: *mut LeanObject,
    mut v_inst_3583_: *mut LeanObject,
    mut v_inst_3584_: *mut LeanObject,
    mut v_inst_3585_: *mut LeanObject,
    mut v_inst_3586_: *mut LeanObject,
    mut v_stx_3587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3588_ = lean_ctor_get(v_inst_3577_, 0);
    lean_inc_ref_n(v_toApplicative_3588_, 2);
    v_toBind_3589_ = lean_ctor_get(v_inst_3577_, 1);
    lean_inc_n(v_toBind_3589_, 3);
    v_getCurrNamespace_3590_ = lean_ctor_get(v_inst_3585_, 0);
    lean_inc(v_getCurrNamespace_3590_);
    v_getOpenDecls_3591_ = lean_ctor_get(v_inst_3585_, 1);
    lean_inc(v_getOpenDecls_3591_);
    lean_dec_ref(v_inst_3585_);
    v___f_3592_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3592_, 0, v_toApplicative_3588_);
    lean_inc(v_inst_3582_);
    v___f_3593_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3593_, 0, v_inst_3582_);
    lean_closure_set(v___f_3593_, 1, v_toBind_3589_);
    lean_closure_set(v___f_3593_, 2, v___f_3592_);
    v___f_3594_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0;
    v___f_3595_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1;
    v___f_3596_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2;
    lean_inc_ref(v_inst_3577_);
    v___x_3597_ = l_StateRefT_x27_instMonad___redArg(v_inst_3577_);
    v___f_3598_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    lean_closure_set(v___f_3598_, 0, v_toApplicative_3588_);
    lean_closure_set(v___f_3598_, 1, v_stx_3587_);
    lean_closure_set(v___f_3598_, 2, v_inst_3582_);
    lean_closure_set(v___f_3598_, 3, v_toBind_3589_);
    lean_closure_set(v___f_3598_, 4, v___f_3593_);
    lean_closure_set(v___f_3598_, 5, v_inst_3579_);
    lean_closure_set(v___f_3598_, 6, v_inst_3577_);
    lean_closure_set(v___f_3598_, 7, v_inst_3578_);
    lean_closure_set(v___f_3598_, 8, v___f_3594_);
    lean_closure_set(v___f_3598_, 9, v___f_3595_);
    lean_closure_set(v___f_3598_, 10, v_inst_3580_);
    lean_closure_set(v___f_3598_, 11, v_inst_3581_);
    lean_closure_set(v___f_3598_, 12, v___x_3597_);
    lean_closure_set(v___f_3598_, 13, v_inst_3586_);
    lean_closure_set(v___f_3598_, 14, v_inst_3583_);
    lean_closure_set(v___f_3598_, 15, v_inst_3584_);
    lean_closure_set(v___f_3598_, 16, v___f_3596_);
    lean_closure_set(v___f_3598_, 17, v_getCurrNamespace_3590_);
    v___x_3599_ = lean_apply_4(
        v_toBind_3589_,
        lean_box(0),
        lean_box(0),
        v_getOpenDecls_3591_,
        v___f_3598_,
    );
    return v___x_3599_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_elabOpenDecl(
    mut v_m_3600_: *mut LeanObject,
    mut v_inst_3601_: *mut LeanObject,
    mut v_inst_3602_: *mut LeanObject,
    mut v_inst_3603_: *mut LeanObject,
    mut v_inst_3604_: *mut LeanObject,
    mut v_inst_3605_: *mut LeanObject,
    mut v_inst_3606_: *mut LeanObject,
    mut v_inst_3607_: *mut LeanObject,
    mut v_inst_3608_: *mut LeanObject,
    mut v_inst_3609_: *mut LeanObject,
    mut v_inst_3610_: *mut LeanObject,
    mut v_stx_3611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3613_: *mut LeanObject,
    mut v_toPure_3614_: *mut LeanObject,
    mut v_s_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    v___x_3616_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3616_, 0, v_a_3613_);
    lean_ctor_set(v___x_3616_, 1, v_s_3615_);
    v___x_3617_ = lean_apply_2(v_toPure_3614_, lean_box(0), v___x_3616_);
    return v___x_3617_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(
    mut v_toPure_3618_: *mut LeanObject,
    mut v_ref_3619_: *mut LeanObject,
    mut v_inst_3620_: *mut LeanObject,
    mut v_toBind_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___f_3623_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3623_, 0, v_a_3622_);
    lean_closure_set(v___f_3623_, 1, v_toPure_3618_);
    v___x_3624_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_3624_, 0, lean_box(0));
    lean_closure_set(v___x_3624_, 1, lean_box(0));
    lean_closure_set(v___x_3624_, 2, v_ref_3619_);
    v___x_3625_ = lean_apply_2(v_inst_3620_, lean_box(0), v___x_3624_);
    v___x_3626_ = lean_apply_4(
        v_toBind_3621_,
        lean_box(0),
        lean_box(0),
        v___x_3625_,
        v___f_3623_,
    );
    return v___x_3626_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(
    mut v_toPure_3627_: *mut LeanObject,
    mut v_inst_3628_: *mut LeanObject,
    mut v_toBind_3629_: *mut LeanObject,
    mut v___x_3630_: *mut LeanObject,
    mut v___x_3631_: *mut LeanObject,
    mut v___x_3632_: *mut LeanObject,
    mut v___x_3633_: *mut LeanObject,
    mut v___x_3634_: *mut LeanObject,
    mut v___f_3635_: *mut LeanObject,
    mut v___x_3636_: *mut LeanObject,
    mut v___x_3637_: *mut LeanObject,
    mut v___x_3638_: *mut LeanObject,
    mut v_nss_3639_: *mut LeanObject,
    mut v_idStx_3640_: *mut LeanObject,
    mut v_ref_3641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100__overap_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_3629_);
    lean_inc(v_ref_3641_);
    v___f_3642_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_3642_, 0, v_toPure_3627_);
    lean_closure_set(v___f_3642_, 1, v_ref_3641_);
    lean_closure_set(v___f_3642_, 2, v_inst_3628_);
    lean_closure_set(v___f_3642_, 3, v_toBind_3629_);
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
    v___x_3644_ = lean_apply_1(v___x_100__overap_3643_, v_ref_3641_);
    v___x_3645_ = lean_apply_4(
        v_toBind_3629_,
        lean_box(0),
        lean_box(0),
        v___x_3644_,
        v___f_3642_,
    );
    return v___x_3645_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(
    mut v_toPure_3646_: *mut LeanObject,
    mut v_____x_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3648_ = lean_ctor_get(v_____x_3647_, 0);
    lean_inc(v_fst_3648_);
    lean_dec_ref(v_____x_3647_);
    v___x_3649_ = lean_apply_2(v_toPure_3646_, lean_box(0), v_fst_3648_);
    return v___x_3649_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(
    mut v_toApplicative_3650_: *mut LeanObject,
    mut v_____do__lift_3651_: *mut LeanObject,
    mut v_inst_3652_: *mut LeanObject,
    mut v_toBind_3653_: *mut LeanObject,
    mut v___x_3654_: *mut LeanObject,
    mut v___x_3655_: *mut LeanObject,
    mut v___x_3656_: *mut LeanObject,
    mut v___x_3657_: *mut LeanObject,
    mut v___x_3658_: *mut LeanObject,
    mut v___f_3659_: *mut LeanObject,
    mut v___x_3660_: *mut LeanObject,
    mut v___x_3661_: *mut LeanObject,
    mut v___x_3662_: *mut LeanObject,
    mut v_nss_3663_: *mut LeanObject,
    mut v_idStx_3664_: *mut LeanObject,
    mut v_____do__lift_3665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_3666_ = lean_ctor_get(v_toApplicative_3650_, 1);
    lean_inc_n(v_toPure_3666_, 2);
    lean_dec_ref(v_toApplicative_3650_);
    v___x_3667_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3667_, 0, v_____do__lift_3651_);
    lean_ctor_set(v___x_3667_, 1, v_____do__lift_3665_);
    v___x_3668_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_3668_, 0, lean_box(0));
    lean_closure_set(v___x_3668_, 1, lean_box(0));
    lean_closure_set(v___x_3668_, 2, v___x_3667_);
    lean_inc(v_inst_3652_);
    v___x_3669_ = lean_apply_2(v_inst_3652_, lean_box(0), v___x_3668_);
    lean_inc_n(v_toBind_3653_, 2);
    v___f_3670_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2 as *mut core::ffi::c_void,
        15,
        14,
    );
    lean_closure_set(v___f_3670_, 0, v_toPure_3666_);
    lean_closure_set(v___f_3670_, 1, v_inst_3652_);
    lean_closure_set(v___f_3670_, 2, v_toBind_3653_);
    lean_closure_set(v___f_3670_, 3, v___x_3654_);
    lean_closure_set(v___f_3670_, 4, v___x_3655_);
    lean_closure_set(v___f_3670_, 5, v___x_3656_);
    lean_closure_set(v___f_3670_, 6, v___x_3657_);
    lean_closure_set(v___f_3670_, 7, v___x_3658_);
    lean_closure_set(v___f_3670_, 8, v___f_3659_);
    lean_closure_set(v___f_3670_, 9, v___x_3660_);
    lean_closure_set(v___f_3670_, 10, v___x_3661_);
    lean_closure_set(v___f_3670_, 11, v___x_3662_);
    lean_closure_set(v___f_3670_, 12, v_nss_3663_);
    lean_closure_set(v___f_3670_, 13, v_idStx_3664_);
    v___f_3671_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3671_, 0, v_toPure_3666_);
    v___x_3672_ = lean_apply_4(
        v_toBind_3653_,
        lean_box(0),
        lean_box(0),
        v___x_3669_,
        v___f_3670_,
    );
    v___x_3673_ = lean_apply_4(
        v_toBind_3653_,
        lean_box(0),
        lean_box(0),
        v___x_3672_,
        v___f_3671_,
    );
    return v___x_3673_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(
    mut v_toApplicative_3674_: *mut LeanObject,
    mut v_inst_3675_: *mut LeanObject,
    mut v_toBind_3676_: *mut LeanObject,
    mut v___x_3677_: *mut LeanObject,
    mut v___x_3678_: *mut LeanObject,
    mut v___x_3679_: *mut LeanObject,
    mut v___x_3680_: *mut LeanObject,
    mut v___x_3681_: *mut LeanObject,
    mut v___f_3682_: *mut LeanObject,
    mut v___x_3683_: *mut LeanObject,
    mut v___x_3684_: *mut LeanObject,
    mut v___x_3685_: *mut LeanObject,
    mut v_nss_3686_: *mut LeanObject,
    mut v_idStx_3687_: *mut LeanObject,
    mut v_getCurrNamespace_3688_: *mut LeanObject,
    mut v_____do__lift_3689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_3676_);
    v___f_3690_ = lean_alloc_closure(
        l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4 as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_3690_, 0, v_toApplicative_3674_);
    lean_closure_set(v___f_3690_, 1, v_____do__lift_3689_);
    lean_closure_set(v___f_3690_, 2, v_inst_3675_);
    lean_closure_set(v___f_3690_, 3, v_toBind_3676_);
    lean_closure_set(v___f_3690_, 4, v___x_3677_);
    lean_closure_set(v___f_3690_, 5, v___x_3678_);
    lean_closure_set(v___f_3690_, 6, v___x_3679_);
    lean_closure_set(v___f_3690_, 7, v___x_3680_);
    lean_closure_set(v___f_3690_, 8, v___x_3681_);
    lean_closure_set(v___f_3690_, 9, v___f_3682_);
    lean_closure_set(v___f_3690_, 10, v___x_3683_);
    lean_closure_set(v___f_3690_, 11, v___x_3684_);
    lean_closure_set(v___f_3690_, 12, v___x_3685_);
    lean_closure_set(v___f_3690_, 13, v_nss_3686_);
    lean_closure_set(v___f_3690_, 14, v_idStx_3687_);
    v___x_3691_ = lean_apply_4(
        v_toBind_3676_,
        lean_box(0),
        lean_box(0),
        v_getCurrNamespace_3688_,
        v___f_3690_,
    );
    return v___x_3691_;
}
pub unsafe fn l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(
    mut v_inst_3692_: *mut LeanObject,
    mut v_inst_3693_: *mut LeanObject,
    mut v_inst_3694_: *mut LeanObject,
    mut v_inst_3695_: *mut LeanObject,
    mut v_inst_3696_: *mut LeanObject,
    mut v_inst_3697_: *mut LeanObject,
    mut v_inst_3698_: *mut LeanObject,
    mut v_inst_3699_: *mut LeanObject,
    mut v_inst_3700_: *mut LeanObject,
    mut v_nss_3701_: *mut LeanObject,
    mut v_idStx_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3703_ = lean_ctor_get(v_inst_3692_, 0);
                lean_inc_ref(v_toApplicative_3703_);
                v_toBind_3704_ = lean_ctor_get(v_inst_3692_, 1);
                lean_inc(v_toBind_3704_);
                v_getCurrNamespace_3705_ = lean_ctor_get(v_inst_3700_, 0);
                v_getOpenDecls_3706_ = lean_ctor_get(v_inst_3700_, 1);
                v_isSharedCheck_3737_ = (!lean_is_exclusive(v_inst_3700_)) as u8;
                if v_isSharedCheck_3737_ == 0 {
                    v___x_3708_ = v_inst_3700_;
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_getOpenDecls_3706_);
                    lean_inc(v_getCurrNamespace_3705_);
                    lean_dec(v_inst_3700_);
                    v___x_3708_ = lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_inst_3692_);
                v___x_3710_ = l_StateRefT_x27_instMonad___redArg(v_inst_3692_);
                v_getEnv_3711_ = lean_ctor_get(v_inst_3693_, 0);
                v_modifyEnv_3712_ = lean_ctor_get(v_inst_3693_, 1);
                v_isSharedCheck_3736_ = (!lean_is_exclusive(v_inst_3693_)) as u8;
                if v_isSharedCheck_3736_ == 0 {
                    v___x_3714_ = v_inst_3693_;
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_modifyEnv_3712_);
                    lean_inc(v_getEnv_3711_);
                    lean_dec(v_inst_3693_);
                    v___x_3714_ = lean_box(0);
                    v_isShared_3715_ = v_isSharedCheck_3736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3716_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0;
                v___f_3717_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3717_, 0, v_modifyEnv_3712_);
                lean_closure_set(v___f_3717_, 1, v___x_3716_);
                v___x_3718_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3718_, 0, lean_box(0));
                lean_closure_set(v___x_3718_, 1, lean_box(0));
                lean_closure_set(v___x_3718_, 2, lean_box(0));
                lean_closure_set(v___x_3718_, 3, lean_box(0));
                lean_closure_set(v___x_3718_, 4, v_getEnv_3711_);
                if v_isShared_3715_ == 0 {
                    lean_ctor_set(v___x_3714_, 1, v___f_3717_);
                    lean_ctor_set(v___x_3714_, 0, v___x_3718_);
                    v___x_3720_ = v___x_3714_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3718_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___f_3717_);
                    v___x_3720_ = v_reuseFailAlloc_3735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_inst_3694_);
                v___f_3721_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_3721_, 0, v_inst_3694_);
                v___f_3722_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_3722_, 0, v_inst_3694_);
                if v_isShared_3709_ == 0 {
                    lean_ctor_set(v___x_3708_, 1, v___f_3722_);
                    lean_ctor_set(v___x_3708_, 0, v___f_3721_);
                    v___x_3724_ = v___x_3708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___f_3721_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___f_3722_);
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
                v___f_3727_ = lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3727_, 0, v_inst_3696_);
                lean_closure_set(v___f_3727_, 1, v___x_3716_);
                lean_inc_ref(v___x_3710_);
                lean_inc_ref(v___f_3727_);
                v___x_3728_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_3727_,
                    v___x_3710_,
                );
                v___x_3729_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3716_, v_inst_3698_);
                v___x_3730_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_3730_, 0, lean_box(0));
                lean_closure_set(v___x_3730_, 1, lean_box(0));
                lean_closure_set(v___x_3730_, 2, lean_box(0));
                lean_closure_set(v___x_3730_, 3, lean_box(0));
                lean_closure_set(v___x_3730_, 4, v_inst_3699_);
                lean_inc(v_inst_3697_);
                v___x_3731_ =
                    l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_3692_, v_inst_3697_);
                lean_inc(v_toBind_3704_);
                v___f_3732_ = lean_alloc_closure(
                    l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                lean_closure_set(v___f_3732_, 0, v_toApplicative_3703_);
                lean_closure_set(v___f_3732_, 1, v_inst_3697_);
                lean_closure_set(v___f_3732_, 2, v_toBind_3704_);
                lean_closure_set(v___f_3732_, 3, v___x_3710_);
                lean_closure_set(v___f_3732_, 4, v___x_3720_);
                lean_closure_set(v___f_3732_, 5, v___x_3724_);
                lean_closure_set(v___f_3732_, 6, v___x_3726_);
                lean_closure_set(v___f_3732_, 7, v___x_3728_);
                lean_closure_set(v___f_3732_, 8, v___f_3727_);
                lean_closure_set(v___f_3732_, 9, v___x_3729_);
                lean_closure_set(v___f_3732_, 10, v___x_3730_);
                lean_closure_set(v___f_3732_, 11, v___x_3731_);
                lean_closure_set(v___f_3732_, 12, v_nss_3701_);
                lean_closure_set(v___f_3732_, 13, v_idStx_3702_);
                lean_closure_set(v___f_3732_, 14, v_getCurrNamespace_3705_);
                v___x_3733_ = lean_apply_4(
                    v_toBind_3704_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_3738_: *mut LeanObject,
    mut v_inst_3739_: *mut LeanObject,
    mut v_inst_3740_: *mut LeanObject,
    mut v_inst_3741_: *mut LeanObject,
    mut v_inst_3742_: *mut LeanObject,
    mut v_inst_3743_: *mut LeanObject,
    mut v_inst_3744_: *mut LeanObject,
    mut v_inst_3745_: *mut LeanObject,
    mut v_inst_3746_: *mut LeanObject,
    mut v_inst_3747_: *mut LeanObject,
    mut v_nss_3748_: *mut LeanObject,
    mut v_idStx_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Elab_Open(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Open(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Open(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Open(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Open(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Open(builtin);
}
