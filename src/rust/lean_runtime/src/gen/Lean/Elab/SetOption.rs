// Lean compiler output
// Module: Lean.Elab.SetOption
// Imports: Lean.Elab.InfoTree Init.Syntax
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNatLit_x3f, l_Lean_Syntax_isStrLit_x3f};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr5, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_panic___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArgs, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Init::System::IO::l_IO_toEIO___boxed;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_DataValue_sameCtor, l_Lean_KVMap_instValueBool, l_Lean_KVMap_instValueDataValue,
};
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Option_get___redArg, l_Lean_Options_set___redArg, l_Lean_getOptionDecl___boxed,
    lean_register_option,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_addCompletionInfo___redArg, l_Lean_Elab_pushInfoLeaf___redArg,
};
use crate::r#gen::Lean::Elab::InfoTree::{
    initialize_Lean_Elab_InfoTree, runtime_initialize_Lean_Elab_InfoTree,
};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_instInhabitedExpr, l_Lean_mkConst};
use crate::r#gen::Lean::Log::l_Lean_logWarning___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [111, 112, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,13546154976408593379 as *mut LeanObject] };
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,4524645600938337447 as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 102, 111, 114, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 111, 112, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,6273911876863363489 as *mut LeanObject] };
static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,12134614065342578556 as *mut LeanObject] };
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject,5633929928404097380 as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 96, 32, 99, 111, 109, 109, 97, 110, 100, 58, 32, 84, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1_value:
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
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__0_value
        ) as *mut LeanObject,
        3136308715950998022 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5_value:
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
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__4_value
        ) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5_value)
        as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9_value:
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
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__8_value
        ) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9_value)
        as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [10, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [10, 98, 117, 116, 32, 116, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [96, 32, 101, 120, 112, 101, 99, 116, 115, 32, 97, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 118, 97, 108, 117, 101, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 84, 104, 101, 32, 118, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 101, 116, 95, 111, 112, 116,
            105, 111, 110, 32, 118, 97, 108, 117, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            96, 59, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 108, 105, 116, 101, 114,
            97, 108, 32, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value: LeanStringObject<
    22,
> = LeanStringObject {
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
        96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 0,
    ],
};
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value: LeanStringObject<
    1,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(
    mut v_name_543_: *mut LeanObject,
    mut v_decl_544_: *mut LeanObject,
    mut v_ref_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_unused_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_547_ = lean_ctor_get(v_decl_544_, 0);
                v_descr_548_ = lean_ctor_get(v_decl_544_, 1);
                v_deprecation_x3f_549_ = lean_ctor_get(v_decl_544_, 2);
                v___x_550_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_551_ = (lean_unbox(v_defValue_547_) as u8);
                lean_ctor_set_uint8(v___x_550_, 0 as u32, v___x_551_);
                lean_inc(v_deprecation_x3f_549_);
                lean_inc_ref(v_descr_548_);
                lean_inc_n(v_name_543_, 2);
                v___x_552_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_552_, 0, v_name_543_);
                lean_ctor_set(v___x_552_, 1, v_ref_545_);
                lean_ctor_set(v___x_552_, 2, v___x_550_);
                lean_ctor_set(v___x_552_, 3, v_descr_548_);
                lean_ctor_set(v___x_552_, 4, v_deprecation_x3f_549_);
                v___x_553_ = lean_register_option(v_name_543_, v___x_552_);
                if lean_obj_tag(v___x_553_) == 0 {
                    v_isSharedCheck_561_ = (!lean_is_exclusive(v___x_553_)) as u8;
                    if v_isSharedCheck_561_ == 0 {
                        v_unused_562_ = lean_ctor_get(v___x_553_, 0);
                        lean_dec(v_unused_562_);
                        v___x_555_ = v___x_553_;
                        v_isShared_556_ = v_isSharedCheck_561_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_553_);
                        v___x_555_ = lean_box(0);
                        v_isShared_556_ = v_isSharedCheck_561_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_543_);
                    v_a_563_ = lean_ctor_get(v___x_553_, 0);
                    v_isSharedCheck_570_ = (!lean_is_exclusive(v___x_553_)) as u8;
                    if v_isSharedCheck_570_ == 0 {
                        v___x_565_ = v___x_553_;
                        v_isShared_566_ = v_isSharedCheck_570_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_563_);
                        lean_dec(v___x_553_);
                        v___x_565_ = lean_box(0);
                        v_isShared_566_ = v_isSharedCheck_570_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_547_);
                v___x_557_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_557_, 0, v_name_543_);
                lean_ctor_set(v___x_557_, 1, v_defValue_547_);
                if v_isShared_556_ == 0 {
                    lean_ctor_set(v___x_555_, 0, v___x_557_);
                    v___x_559_ = v___x_555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
                    v___x_559_ = v_reuseFailAlloc_560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_559_;
            }
            3 => {
                if v_isShared_566_ == 0 {
                    v___x_568_ = v___x_565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
                    v___x_568_ = v_reuseFailAlloc_569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_571_: *mut LeanObject,
    mut v_decl_572_: *mut LeanObject,
    mut v_ref_573_: *mut LeanObject,
    mut v_a_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v_name_571_, v_decl_572_, v_ref_573_);
    lean_dec_ref(v_decl_572_);
    return v_res_575_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_598_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_;
    v___x_599_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_;
    v___x_600_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_;
    v___x_601_ = l_Lean_Option_register___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4__spec__0(v___x_598_, v___x_599_, v___x_600_);
    return v___x_601_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4____boxed(
    mut v_a_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_res_603_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
    return v_res_603_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    v___x_605_ =
        l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__0;
    v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
    return v___x_606_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ =
        l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__2;
    v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
    return v___x_609_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(
    mut v_inst_610_: *mut LeanObject,
    mut v_inst_611_: *mut LeanObject,
    mut v_optionName_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_613_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__1);
    v___x_614_ = l_Lean_MessageData_ofName(v_optionName_612_);
    v___x_615_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_615_, 0, v___x_613_);
    lean_ctor_set(v___x_615_, 1, v___x_614_);
    v___x_616_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg___closed__3);
    v___x_617_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_617_, 0, v___x_615_);
    lean_ctor_set(v___x_617_, 1, v___x_616_);
    v___x_618_ = l_Lean_throwError___redArg(v_inst_610_, v_inst_611_, v___x_617_);
    return v___x_618_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable(
    mut v_m_619_: *mut LeanObject,
    mut v_inst_620_: *mut LeanObject,
    mut v_inst_621_: *mut LeanObject,
    mut v_00_u03b1_622_: *mut LeanObject,
    mut v_optionName_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(
        v_inst_620_,
        v_inst_621_,
        v_optionName_623_,
    );
    return v___x_624_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2()
-> *mut LeanObject {
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_628_ = lean_box(0);
    v___x_629_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__1;
    v___x_630_ = l_Lean_mkConst(v___x_629_, v___x_628_);
    return v___x_630_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2_once
        ),
        _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__2,
    );
    v___x_632_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_632_, 0, v___x_631_);
    return v___x_632_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6()
-> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = lean_box(0);
    v___x_637_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__5;
    v___x_638_ = l_Lean_mkConst(v___x_637_, v___x_636_);
    return v___x_638_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7()
-> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6_once
        ),
        _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__6,
    );
    v___x_640_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_640_, 0, v___x_639_);
    return v___x_640_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10()
-> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = lean_box(0);
    v___x_645_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__9;
    v___x_646_ = l_Lean_mkConst(v___x_645_, v___x_644_);
    return v___x_646_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11()
-> *mut LeanObject {
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    v___x_647_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10_once
        ),
        _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__10,
    );
    v___x_648_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_648_, 0, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(
    mut v_x_649_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_649_) {
        0 => {
            let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
            v___x_650_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3_once
                ),
                _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__3,
            );
            return v___x_650_;
        }
        1 => {
            let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
            v___x_651_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7_once
                ),
                _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__7,
            );
            return v___x_651_;
        }
        3 => {
            let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
            v___x_652_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11_once
                ),
                _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___closed__11,
            );
            return v___x_652_;
        }
        _ => {
            let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
            v___x_653_ = lean_box(0);
            return v___x_653_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f___boxed(
    mut v_x_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_655_: *mut LeanObject = core::ptr::null_mut();
    v_res_655_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_x_654_);
    lean_dec_ref(v_x_654_);
    return v_res_655_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    v___x_657_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__0;
    v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
    return v___x_658_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_660_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__2;
    v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
    return v___x_661_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    v___x_663_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__4;
    v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
    return v___x_664_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    v___x_666_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__6;
    v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
    return v___x_667_;
}
pub unsafe fn _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__16;
    v___x_681_ = lean_unsigned_to_nat(14);
    v___x_682_ = lean_unsigned_to_nat(22);
    v___x_683_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__15;
    v___x_684_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__14;
    v___x_685_ =
        l_mkPanicMessageWithDecl(v___x_684_, v___x_683_, v___x_682_, v___x_681_, v___x_680_);
    return v___x_685_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(
    mut v_inst_686_: *mut LeanObject,
    mut v_inst_687_: *mut LeanObject,
    mut v_optionName_688_: *mut LeanObject,
    mut v_found_689_: *mut LeanObject,
    mut v_defVal_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_v_726_: u8 = 0;
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut v_v_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_744_: u8 = 0;
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut v_v_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_758_: u8 = 0;
    let mut v_v_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_691_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_690_);
                if lean_obj_tag(v___x_691_) == 1 {
                    v_val_692_ = lean_ctor_get(v___x_691_, 0);
                    lean_inc(v_val_692_);
                    lean_dec_ref_known(v___x_691_, 1);
                    v___x_763_ =
                        l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_689_);
                    if lean_obj_tag(v___x_763_) == 0 {
                        v___x_764_ = l_Lean_instInhabitedExpr;
                        v___x_765_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__17);
                        v___x_766_ = l_panic___redArg(v___x_764_, v___x_765_);
                        v___y_715_ = v___x_766_;
                        state = 2;
                        continue;
                    } else {
                        v_val_767_ = lean_ctor_get(v___x_763_, 0);
                        lean_inc(v_val_767_);
                        lean_dec_ref_known(v___x_763_, 1);
                        v___y_715_ = v_val_767_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_691_);
                    lean_dec_ref(v_found_689_);
                    v___x_768_ =
                        l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(
                            v_inst_686_,
                            v_inst_687_,
                            v_optionName_688_,
                        );
                    return v___x_768_;
                }
            }
            1 => {
                v___x_697_ = l_Lean_MessageData_ofFormat(v___y_696_);
                v___x_698_ = l_Lean_indentD(v___x_697_);
                lean_inc_ref(v___y_694_);
                v___x_699_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_699_, 0, v___y_694_);
                lean_ctor_set(v___x_699_, 1, v___x_698_);
                v___x_700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__1);
                v___x_701_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_701_, 0, v___x_699_);
                lean_ctor_set(v___x_701_, 1, v___x_700_);
                v___x_702_ = l_Lean_MessageData_ofExpr(v___y_695_);
                v___x_703_ = l_Lean_indentD(v___x_702_);
                v___x_704_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_704_, 0, v___x_701_);
                lean_ctor_set(v___x_704_, 1, v___x_703_);
                v___x_705_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__3);
                v___x_706_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_706_, 0, v___x_704_);
                lean_ctor_set(v___x_706_, 1, v___x_705_);
                v___x_707_ = l_Lean_MessageData_ofName(v_optionName_688_);
                v___x_708_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_708_, 0, v___x_706_);
                lean_ctor_set(v___x_708_, 1, v___x_707_);
                v___x_709_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__5);
                v___x_710_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_710_, 0, v___x_708_);
                lean_ctor_set(v___x_710_, 1, v___x_709_);
                v___x_711_ = l_Lean_indentExpr(v_val_692_);
                v___x_712_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_712_, 0, v___x_710_);
                lean_ctor_set(v___x_712_, 1, v___x_711_);
                v___x_713_ = l_Lean_throwError___redArg(v_inst_686_, v_inst_687_, v___x_712_);
                return v___x_713_;
            }
            2 => {
                v___x_716_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7_once), _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__7);
                match lean_obj_tag(v_found_689_) {
                    0 => {
                        v_v_717_ = lean_ctor_get(v_found_689_, 0);
                        v_isSharedCheck_725_ = (!lean_is_exclusive(v_found_689_)) as u8;
                        if v_isSharedCheck_725_ == 0 {
                            v___x_719_ = v_found_689_;
                            v_isShared_720_ = v_isSharedCheck_725_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_v_717_);
                            lean_dec(v_found_689_);
                            v___x_719_ = lean_box(0);
                            v_isShared_720_ = v_isSharedCheck_725_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_v_726_ = lean_ctor_get_uint8(v_found_689_, 0 as u32);
                        lean_dec_ref_known(v_found_689_, 0);
                        if v_v_726_ == 0 {
                            v___x_727_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__9;
                            v___y_694_ = v___x_716_;
                            v___y_695_ = v___y_715_;
                            v___y_696_ = v___x_727_;
                            state = 1;
                            continue;
                        } else {
                            v___x_728_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__11;
                            v___y_694_ = v___x_716_;
                            v___y_695_ = v___y_715_;
                            v___y_696_ = v___x_728_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_v_729_ = lean_ctor_get(v_found_689_, 0);
                        v_isSharedCheck_740_ = (!lean_is_exclusive(v_found_689_)) as u8;
                        if v_isSharedCheck_740_ == 0 {
                            v___x_731_ = v_found_689_;
                            v_isShared_732_ = v_isSharedCheck_740_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_v_729_);
                            lean_dec(v_found_689_);
                            v___x_731_ = lean_box(0);
                            v_isShared_732_ = v_isSharedCheck_740_;
                            state = 5;
                            continue;
                        }
                    }
                    3 => {
                        v_v_741_ = lean_ctor_get(v_found_689_, 0);
                        v_isSharedCheck_749_ = (!lean_is_exclusive(v_found_689_)) as u8;
                        if v_isSharedCheck_749_ == 0 {
                            v___x_743_ = v_found_689_;
                            v_isShared_744_ = v_isSharedCheck_749_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_v_741_);
                            lean_dec(v_found_689_);
                            v___x_743_ = lean_box(0);
                            v_isShared_744_ = v_isSharedCheck_749_;
                            state = 7;
                            continue;
                        }
                    }
                    4 => {
                        v_v_750_ = lean_ctor_get(v_found_689_, 0);
                        v_isSharedCheck_758_ = (!lean_is_exclusive(v_found_689_)) as u8;
                        if v_isSharedCheck_758_ == 0 {
                            v___x_752_ = v_found_689_;
                            v_isShared_753_ = v_isSharedCheck_758_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_v_750_);
                            lean_dec(v_found_689_);
                            v___x_752_ = lean_box(0);
                            v_isShared_753_ = v_isSharedCheck_758_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_v_759_ = lean_ctor_get(v_found_689_, 0);
                        lean_inc(v_v_759_);
                        lean_dec_ref_known(v_found_689_, 1);
                        v___x_760_ = lean_box(0);
                        v___x_761_ = 0;
                        v___x_762_ = l_Lean_Syntax_formatStx(v_v_759_, v___x_760_, v___x_761_);
                        v___y_694_ = v___x_716_;
                        v___y_695_ = v___y_715_;
                        v___y_696_ = v___x_762_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_721_ = l_String_quote(v_v_717_);
                if v_isShared_720_ == 0 {
                    lean_ctor_set_tag(v___x_719_, 3);
                    lean_ctor_set(v___x_719_, 0, v___x_721_);
                    v___x_723_ = v___x_719_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
                    v___x_723_ = v_reuseFailAlloc_724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_694_ = v___x_716_;
                v___y_695_ = v___y_715_;
                v___y_696_ = v___x_723_;
                state = 1;
                continue;
            }
            5 => {
                v___x_733_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__13;
                v___x_734_ = 1;
                v___x_735_ = l_Lean_Name_toString(v_v_729_, v___x_734_);
                if v_isShared_732_ == 0 {
                    lean_ctor_set_tag(v___x_731_, 3);
                    lean_ctor_set(v___x_731_, 0, v___x_735_);
                    v___x_737_ = v___x_731_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
                    v___x_737_ = v_reuseFailAlloc_739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_738_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_738_, 0, v___x_733_);
                lean_ctor_set(v___x_738_, 1, v___x_737_);
                v___y_694_ = v___x_716_;
                v___y_695_ = v___y_715_;
                v___y_696_ = v___x_738_;
                state = 1;
                continue;
            }
            7 => {
                v___x_745_ = l_Nat_reprFast(v_v_741_);
                if v_isShared_744_ == 0 {
                    lean_ctor_set(v___x_743_, 0, v___x_745_);
                    v___x_747_ = v___x_743_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_748_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
                    v___x_747_ = v_reuseFailAlloc_748_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_694_ = v___x_716_;
                v___y_695_ = v___y_715_;
                v___y_696_ = v___x_747_;
                state = 1;
                continue;
            }
            9 => {
                v___x_754_ = l_Int_repr(v_v_750_);
                lean_dec(v_v_750_);
                if v_isShared_753_ == 0 {
                    lean_ctor_set_tag(v___x_752_, 3);
                    lean_ctor_set(v___x_752_, 0, v___x_754_);
                    v___x_756_ = v___x_752_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_757_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
                    v___x_756_ = v_reuseFailAlloc_757_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_694_ = v___x_716_;
                v___y_695_ = v___y_715_;
                v___y_696_ = v___x_756_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___boxed(
    mut v_inst_769_: *mut LeanObject,
    mut v_inst_770_: *mut LeanObject,
    mut v_optionName_771_: *mut LeanObject,
    mut v_found_772_: *mut LeanObject,
    mut v_defVal_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_769_, v_inst_770_, v_optionName_771_, v_found_772_, v_defVal_773_);
    lean_dec_ref(v_defVal_773_);
    return v_res_774_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(
    mut v_m_775_: *mut LeanObject,
    mut v_inst_776_: *mut LeanObject,
    mut v_inst_777_: *mut LeanObject,
    mut v_optionName_778_: *mut LeanObject,
    mut v_found_779_: *mut LeanObject,
    mut v_defVal_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___x_781_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_776_, v_inst_777_, v_optionName_778_, v_found_779_, v_defVal_780_);
    return v___x_781_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___boxed(
    mut v_m_782_: *mut LeanObject,
    mut v_inst_783_: *mut LeanObject,
    mut v_inst_784_: *mut LeanObject,
    mut v_optionName_785_: *mut LeanObject,
    mut v_found_786_: *mut LeanObject,
    mut v_defVal_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_788_: *mut LeanObject = core::ptr::null_mut();
    v_res_788_ =
        l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue(
            v_m_782_,
            v_inst_783_,
            v_inst_784_,
            v_optionName_785_,
            v_found_786_,
            v_defVal_787_,
        );
    lean_dec_ref(v_defVal_787_);
    return v_res_788_;
}
pub unsafe fn l_Lean_Elab_validateOptionValue___redArg(
    mut v_inst_789_: *mut LeanObject,
    mut v_inst_790_: *mut LeanObject,
    mut v_optionName_791_: *mut LeanObject,
    mut v_decl_792_: *mut LeanObject,
    mut v_val_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    v_defValue_794_ = lean_ctor_get(v_decl_792_, 2);
    v___x_795_ = l_Lean_DataValue_sameCtor(v_defValue_794_, v_val_793_);
    if v___x_795_ == 0 {
        let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
        v___x_796_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg(v_inst_789_, v_inst_790_, v_optionName_791_, v_val_793_, v_defValue_794_);
        return v___x_796_;
    } else {
        let mut v_toApplicative_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_val_793_);
        lean_dec(v_optionName_791_);
        lean_dec_ref(v_inst_790_);
        v_toApplicative_797_ = lean_ctor_get(v_inst_789_, 0);
        lean_inc_ref(v_toApplicative_797_);
        lean_dec_ref(v_inst_789_);
        v_toPure_798_ = lean_ctor_get(v_toApplicative_797_, 1);
        lean_inc(v_toPure_798_);
        lean_dec_ref(v_toApplicative_797_);
        v___x_799_ = lean_box(0);
        v___x_800_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_799_);
        return v___x_800_;
    }
}
pub unsafe fn l_Lean_Elab_validateOptionValue___redArg___boxed(
    mut v_inst_801_: *mut LeanObject,
    mut v_inst_802_: *mut LeanObject,
    mut v_optionName_803_: *mut LeanObject,
    mut v_decl_804_: *mut LeanObject,
    mut v_val_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_Elab_validateOptionValue___redArg(
        v_inst_801_,
        v_inst_802_,
        v_optionName_803_,
        v_decl_804_,
        v_val_805_,
    );
    lean_dec_ref(v_decl_804_);
    return v_res_806_;
}
pub unsafe fn l_Lean_Elab_validateOptionValue(
    mut v_m_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_inst_809_: *mut LeanObject,
    mut v_optionName_810_: *mut LeanObject,
    mut v_decl_811_: *mut LeanObject,
    mut v_val_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v___x_813_ = l_Lean_Elab_validateOptionValue___redArg(
        v_inst_808_,
        v_inst_809_,
        v_optionName_810_,
        v_decl_811_,
        v_val_812_,
    );
    return v___x_813_;
}
pub unsafe fn l_Lean_Elab_validateOptionValue___boxed(
    mut v_m_814_: *mut LeanObject,
    mut v_inst_815_: *mut LeanObject,
    mut v_inst_816_: *mut LeanObject,
    mut v_optionName_817_: *mut LeanObject,
    mut v_decl_818_: *mut LeanObject,
    mut v_val_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_820_: *mut LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Lean_Elab_validateOptionValue(
        v_m_814_,
        v_inst_815_,
        v_inst_816_,
        v_optionName_817_,
        v_decl_818_,
        v_val_819_,
    );
    lean_dec_ref(v_decl_818_);
    return v_res_820_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0(
    mut v___x_821_: *mut LeanObject,
    mut v_optionName_822_: *mut LeanObject,
    mut v_val_823_: *mut LeanObject,
    mut v_decl_824_: *mut LeanObject,
    mut v_toPure_825_: *mut LeanObject,
    mut v_____do__lift_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = l_Lean_Options_set___redArg(
        v___x_821_,
        v_____do__lift_826_,
        v_optionName_822_,
        v_val_823_,
    );
    v___x_828_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_828_, 0, v___x_827_);
    lean_ctor_set(v___x_828_, 1, v_decl_824_);
    v___x_829_ = lean_apply_2(v_toPure_825_, lean_box(0), v___x_828_);
    return v___x_829_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1(
    mut v_toBind_830_: *mut LeanObject,
    mut v_inst_831_: *mut LeanObject,
    mut v___f_832_: *mut LeanObject,
    mut v_____r_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    v___x_834_ = lean_apply_4(
        v_toBind_830_,
        lean_box(0),
        lean_box(0),
        v_inst_831_,
        v___f_832_,
    );
    return v___x_834_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(
    mut v_inst_835_: *mut LeanObject,
    mut v_inst_836_: *mut LeanObject,
    mut v_inst_837_: *mut LeanObject,
    mut v_optionName_838_: *mut LeanObject,
    mut v_decl_839_: *mut LeanObject,
    mut v_val_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_841_ = l_Lean_KVMap_instValueDataValue;
    v_toApplicative_842_ = lean_ctor_get(v_inst_835_, 0);
    v_toBind_843_ = lean_ctor_get(v_inst_835_, 1);
    lean_inc_n(v_toBind_843_, 2);
    v_toPure_844_ = lean_ctor_get(v_toApplicative_842_, 1);
    lean_inc(v_toPure_844_);
    lean_inc_ref(v_val_840_);
    lean_inc(v_optionName_838_);
    v___x_845_ = l_Lean_Elab_validateOptionValue___redArg(
        v_inst_835_,
        v_inst_837_,
        v_optionName_838_,
        v_decl_839_,
        v_val_840_,
    );
    v___f_846_ = lean_alloc_closure(
        l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_846_, 0, v___x_841_);
    lean_closure_set(v___f_846_, 1, v_optionName_838_);
    lean_closure_set(v___f_846_, 2, v_val_840_);
    lean_closure_set(v___f_846_, 3, v_decl_839_);
    lean_closure_set(v___f_846_, 4, v_toPure_844_);
    v___f_847_ = lean_alloc_closure(
        l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_847_, 0, v_toBind_843_);
    lean_closure_set(v___f_847_, 1, v_inst_836_);
    lean_closure_set(v___f_847_, 2, v___f_846_);
    v___x_848_ = lean_apply_4(
        v_toBind_843_,
        lean_box(0),
        lean_box(0),
        v___x_845_,
        v___f_847_,
    );
    return v___x_848_;
}
pub unsafe fn l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption(
    mut v_m_849_: *mut LeanObject,
    mut v_inst_850_: *mut LeanObject,
    mut v_inst_851_: *mut LeanObject,
    mut v_inst_852_: *mut LeanObject,
    mut v_optionName_853_: *mut LeanObject,
    mut v_decl_854_: *mut LeanObject,
    mut v_val_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_856_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(
        v_inst_850_,
        v_inst_851_,
        v_inst_852_,
        v_optionName_853_,
        v_decl_854_,
        v_val_855_,
    );
    return v___x_856_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__0(
    mut v_ref_857_: *mut LeanObject,
    mut v_ex_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = lean_io_error_to_string(v_ex_858_);
    v___x_860_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_860_, 0, v___x_859_);
    v___x_861_ = l_Lean_MessageData_ofFormat(v___x_860_);
    v___x_862_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_862_, 0, v_ref_857_);
    lean_ctor_set(v___x_862_, 1, v___x_861_);
    return v___x_862_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0;
    v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
    return v___x_865_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2;
    v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__12;
    v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
    return v___x_870_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__1(
    mut v_val_871_: *mut LeanObject,
    mut v_defValue_872_: *mut LeanObject,
    mut v_inst_873_: *mut LeanObject,
    mut v_inst_874_: *mut LeanObject,
    mut v_optionName_875_: *mut LeanObject,
    mut v_inst_876_: *mut LeanObject,
    mut v_decl_877_: *mut LeanObject,
    mut v_____r_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: u8 = 0;
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_val_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_916_: u8 = 0;
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Syntax_isStrLit_x3f(v_val_871_);
                if lean_obj_tag(v___x_893_) == 0 {
                    v___x_894_ = l_Lean_Syntax_isNatLit_x3f(v_val_871_);
                    if lean_obj_tag(v___x_894_) == 0 {
                        if lean_obj_tag(v_val_871_) == 2 {
                            v_val_895_ = lean_ctor_get(v_val_871_, 1);
                            v___x_896_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__10;
                            v___x_897_ = lean_string_dec_eq(v_val_895_, v___x_896_);
                            if v___x_897_ == 0 {
                                v___x_898_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___redArg___closed__8;
                                v___x_899_ = lean_string_dec_eq(v_val_895_, v___x_898_);
                                if v___x_899_ == 0 {
                                    lean_dec_ref(v_decl_877_);
                                    lean_dec(v_inst_876_);
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v_val_871_, 2);
                                    v___x_900_ = lean_alloc_ctor(1, 0, (1) as u32);
                                    lean_ctor_set_uint8(v___x_900_, 0 as u32, v___x_897_);
                                    v___x_901_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_873_, v_inst_876_, v_inst_874_, v_optionName_875_, v_decl_877_, v___x_900_);
                                    return v___x_901_;
                                }
                            } else {
                                lean_dec_ref_known(v_val_871_, 2);
                                v___x_902_ = lean_alloc_ctor(1, 0, (1) as u32);
                                lean_ctor_set_uint8(v___x_902_, 0 as u32, v___x_897_);
                                v___x_903_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(v_inst_873_, v_inst_876_, v_inst_874_, v_optionName_875_, v_decl_877_, v___x_902_);
                                return v___x_903_;
                            }
                        } else {
                            lean_dec_ref(v_decl_877_);
                            lean_dec(v_inst_876_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_871_);
                        v_val_904_ = lean_ctor_get(v___x_894_, 0);
                        v_isSharedCheck_912_ = (!lean_is_exclusive(v___x_894_)) as u8;
                        if v_isSharedCheck_912_ == 0 {
                            v___x_906_ = v___x_894_;
                            v_isShared_907_ = v_isSharedCheck_912_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_904_);
                            lean_dec(v___x_894_);
                            v___x_906_ = lean_box(0);
                            v_isShared_907_ = v_isSharedCheck_912_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_871_);
                    v_val_913_ = lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_921_ = (!lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_921_ == 0 {
                        v___x_915_ = v___x_893_;
                        v_isShared_916_ = v_isSharedCheck_921_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_913_);
                        lean_dec(v___x_893_);
                        v___x_915_ = lean_box(0);
                        v_isShared_916_ = v_isSharedCheck_921_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_880_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_872_);
                if lean_obj_tag(v___x_880_) == 1 {
                    lean_dec(v_optionName_875_);
                    v_val_881_ = lean_ctor_get(v___x_880_, 0);
                    lean_inc(v_val_881_);
                    lean_dec_ref_known(v___x_880_, 1);
                    v___x_882_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1,
                    );
                    v___x_883_ = l_Lean_MessageData_ofSyntax(v_val_871_);
                    v___x_884_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_884_, 0, v___x_882_);
                    lean_ctor_set(v___x_884_, 1, v___x_883_);
                    v___x_885_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3,
                    );
                    v___x_886_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_886_, 0, v___x_884_);
                    lean_ctor_set(v___x_886_, 1, v___x_885_);
                    v___x_887_ = l_Lean_MessageData_ofExpr(v_val_881_);
                    v___x_888_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_888_, 0, v___x_886_);
                    lean_ctor_set(v___x_888_, 1, v___x_887_);
                    v___x_889_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once
                        ),
                        _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4,
                    );
                    v___x_890_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_890_, 0, v___x_888_);
                    lean_ctor_set(v___x_890_, 1, v___x_889_);
                    v___x_891_ = l_Lean_throwError___redArg(v_inst_873_, v_inst_874_, v___x_890_);
                    return v___x_891_;
                } else {
                    lean_dec(v___x_880_);
                    lean_dec(v_val_871_);
                    v___x_892_ =
                        l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___redArg(
                            v_inst_873_,
                            v_inst_874_,
                            v_optionName_875_,
                        );
                    return v___x_892_;
                }
            }
            2 => {
                if v_isShared_907_ == 0 {
                    lean_ctor_set_tag(v___x_906_, 3);
                    v___x_909_ = v___x_906_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_904_);
                    v___x_909_ = v_reuseFailAlloc_911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_910_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(
                        v_inst_873_,
                        v_inst_876_,
                        v_inst_874_,
                        v_optionName_875_,
                        v_decl_877_,
                        v___x_909_,
                    );
                return v___x_910_;
            }
            4 => {
                if v_isShared_916_ == 0 {
                    lean_ctor_set_tag(v___x_915_, 0);
                    v___x_918_ = v___x_915_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_920_, 0, v_val_913_);
                    v___x_918_ = v_reuseFailAlloc_920_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_919_ =
                    l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___redArg(
                        v_inst_873_,
                        v_inst_876_,
                        v_inst_874_,
                        v_optionName_875_,
                        v_decl_877_,
                        v___x_918_,
                    );
                return v___x_919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(
    mut v_val_922_: *mut LeanObject,
    mut v_defValue_923_: *mut LeanObject,
    mut v_inst_924_: *mut LeanObject,
    mut v_inst_925_: *mut LeanObject,
    mut v_optionName_926_: *mut LeanObject,
    mut v_inst_927_: *mut LeanObject,
    mut v_decl_928_: *mut LeanObject,
    mut v_____r_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_930_: *mut LeanObject = core::ptr::null_mut();
    v_res_930_ = l_Lean_Elab_elabSetOption___redArg___lam__1(
        v_val_922_,
        v_defValue_923_,
        v_inst_924_,
        v_inst_925_,
        v_optionName_926_,
        v_inst_927_,
        v_decl_928_,
        v_____r_929_,
    );
    lean_dec_ref(v_defValue_923_);
    return v_res_930_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__2(
    mut v_val_931_: *mut LeanObject,
    mut v_inst_932_: *mut LeanObject,
    mut v_inst_933_: *mut LeanObject,
    mut v_optionName_934_: *mut LeanObject,
    mut v_inst_935_: *mut LeanObject,
    mut v_id_936_: *mut LeanObject,
    mut v_inst_937_: *mut LeanObject,
    mut v_toBind_938_: *mut LeanObject,
    mut v_decl_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    v_declName_940_ = lean_ctor_get(v_decl_939_, 1);
    lean_inc(v_declName_940_);
    v_defValue_941_ = lean_ctor_get(v_decl_939_, 2);
    lean_inc_ref(v_defValue_941_);
    lean_inc(v_optionName_934_);
    lean_inc_ref(v_inst_932_);
    v___f_942_ = lean_alloc_closure(
        l_Lean_Elab_elabSetOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_942_, 0, v_val_931_);
    lean_closure_set(v___f_942_, 1, v_defValue_941_);
    lean_closure_set(v___f_942_, 2, v_inst_932_);
    lean_closure_set(v___f_942_, 3, v_inst_933_);
    lean_closure_set(v___f_942_, 4, v_optionName_934_);
    lean_closure_set(v___f_942_, 5, v_inst_935_);
    lean_closure_set(v___f_942_, 6, v_decl_939_);
    v___x_943_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_943_, 0, v_id_936_);
    lean_ctor_set(v___x_943_, 1, v_optionName_934_);
    lean_ctor_set(v___x_943_, 2, v_declName_940_);
    v___x_944_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_944_, 0, v___x_943_);
    v___x_945_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_932_, v_inst_937_, v___x_944_);
    v___x_946_ = lean_apply_4(
        v_toBind_938_,
        lean_box(0),
        lean_box(0),
        v___x_945_,
        v___f_942_,
    );
    return v___x_946_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__3(
    mut v_id_947_: *mut LeanObject,
    mut v_val_948_: *mut LeanObject,
    mut v_inst_949_: *mut LeanObject,
    mut v_inst_950_: *mut LeanObject,
    mut v_inst_951_: *mut LeanObject,
    mut v_inst_952_: *mut LeanObject,
    mut v_toBind_953_: *mut LeanObject,
    mut v___f_954_: *mut LeanObject,
    mut v_inst_955_: *mut LeanObject,
    mut v_____r_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionName_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v___x_957_ = l_Lean_Syntax_getId(v_id_947_);
    v_optionName_958_ = lean_erase_macro_scopes(v___x_957_);
    lean_inc(v_toBind_953_);
    lean_inc(v_optionName_958_);
    v___f_959_ = lean_alloc_closure(
        l_Lean_Elab_elabSetOption___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_959_, 0, v_val_948_);
    lean_closure_set(v___f_959_, 1, v_inst_949_);
    lean_closure_set(v___f_959_, 2, v_inst_950_);
    lean_closure_set(v___f_959_, 3, v_optionName_958_);
    lean_closure_set(v___f_959_, 4, v_inst_951_);
    lean_closure_set(v___f_959_, 5, v_id_947_);
    lean_closure_set(v___f_959_, 6, v_inst_952_);
    lean_closure_set(v___f_959_, 7, v_toBind_953_);
    v___x_960_ = lean_alloc_closure(l_Lean_getOptionDecl___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_960_, 0, v_optionName_958_);
    v___x_961_ = lean_alloc_closure(l_IO_toEIO___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_961_, 0, lean_box(0));
    lean_closure_set(v___x_961_, 1, lean_box(0));
    lean_closure_set(v___x_961_, 2, v___f_954_);
    lean_closure_set(v___x_961_, 3, v___x_960_);
    v___x_962_ = lean_apply_2(v_inst_955_, lean_box(0), v___x_961_);
    v___x_963_ = lean_apply_4(
        v_toBind_953_,
        lean_box(0),
        lean_box(0),
        v___x_962_,
        v___f_959_,
    );
    return v___x_963_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg___lam__4(
    mut v_id_964_: *mut LeanObject,
    mut v_val_965_: *mut LeanObject,
    mut v_inst_966_: *mut LeanObject,
    mut v_inst_967_: *mut LeanObject,
    mut v_inst_968_: *mut LeanObject,
    mut v_inst_969_: *mut LeanObject,
    mut v_toBind_970_: *mut LeanObject,
    mut v_inst_971_: *mut LeanObject,
    mut v_ref_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ref_972_);
    v___f_973_ = lean_alloc_closure(
        l_Lean_Elab_elabSetOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_973_, 0, v_ref_972_);
    lean_inc(v_toBind_970_);
    lean_inc_ref(v_inst_969_);
    lean_inc_ref(v_inst_966_);
    v___f_974_ = lean_alloc_closure(
        l_Lean_Elab_elabSetOption___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_974_, 0, v_id_964_);
    lean_closure_set(v___f_974_, 1, v_val_965_);
    lean_closure_set(v___f_974_, 2, v_inst_966_);
    lean_closure_set(v___f_974_, 3, v_inst_967_);
    lean_closure_set(v___f_974_, 4, v_inst_968_);
    lean_closure_set(v___f_974_, 5, v_inst_969_);
    lean_closure_set(v___f_974_, 6, v_toBind_970_);
    lean_closure_set(v___f_974_, 7, v___f_973_);
    lean_closure_set(v___f_974_, 8, v_inst_971_);
    v___x_975_ = l_Lean_Syntax_getArgs(v_ref_972_);
    v___x_976_ = lean_unsigned_to_nat(3);
    v___x_977_ = lean_unsigned_to_nat(0);
    v___x_978_ = l_Array_toSubarray___redArg(v___x_975_, v___x_977_, v___x_976_);
    v___x_979_ = l_Subarray_copy___redArg(v___x_978_);
    v___x_980_ = l_Lean_Syntax_setArgs(v_ref_972_, v___x_979_);
    v___x_981_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_981_, 0, v___x_980_);
    v___x_982_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_966_, v_inst_969_, v___x_981_);
    v___x_983_ = lean_apply_4(
        v_toBind_970_,
        lean_box(0),
        lean_box(0),
        v___x_982_,
        v___f_974_,
    );
    return v___x_983_;
}
pub unsafe fn l_Lean_Elab_elabSetOption___redArg(
    mut v_inst_984_: *mut LeanObject,
    mut v_inst_985_: *mut LeanObject,
    mut v_inst_986_: *mut LeanObject,
    mut v_inst_987_: *mut LeanObject,
    mut v_inst_988_: *mut LeanObject,
    mut v_id_989_: *mut LeanObject,
    mut v_val_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_991_ = lean_ctor_get(v_inst_986_, 1);
    v_toBind_992_ = lean_ctor_get(v_inst_984_, 1);
    lean_inc_n(v_toBind_992_, 2);
    v_getRef_993_ = lean_ctor_get(v_toMonadRef_991_, 0);
    lean_inc(v_getRef_993_);
    v___f_994_ = lean_alloc_closure(
        l_Lean_Elab_elabSetOption___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_994_, 0, v_id_989_);
    lean_closure_set(v___f_994_, 1, v_val_990_);
    lean_closure_set(v___f_994_, 2, v_inst_984_);
    lean_closure_set(v___f_994_, 3, v_inst_986_);
    lean_closure_set(v___f_994_, 4, v_inst_985_);
    lean_closure_set(v___f_994_, 5, v_inst_988_);
    lean_closure_set(v___f_994_, 6, v_toBind_992_);
    lean_closure_set(v___f_994_, 7, v_inst_987_);
    v___x_995_ = lean_apply_4(
        v_toBind_992_,
        lean_box(0),
        lean_box(0),
        v_getRef_993_,
        v___f_994_,
    );
    return v___x_995_;
}
pub unsafe fn l_Lean_Elab_elabSetOption(
    mut v_m_996_: *mut LeanObject,
    mut v_inst_997_: *mut LeanObject,
    mut v_inst_998_: *mut LeanObject,
    mut v_inst_999_: *mut LeanObject,
    mut v_inst_1000_: *mut LeanObject,
    mut v_inst_1001_: *mut LeanObject,
    mut v_id_1002_: *mut LeanObject,
    mut v_val_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lean_Elab_elabSetOption___redArg(
        v_inst_997_,
        v_inst_998_,
        v_inst_999_,
        v_inst_1000_,
        v_inst_1001_,
        v_id_1002_,
        v_val_1003_,
    );
    return v___x_1004_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__0;
    v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__2;
    v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__4;
    v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(
    mut v___x_1014_: *mut LeanObject,
    mut v_toApplicative_1015_: *mut LeanObject,
    mut v_decl_1016_: *mut LeanObject,
    mut v_optionName_1017_: *mut LeanObject,
    mut v_inst_1018_: *mut LeanObject,
    mut v_inst_1019_: *mut LeanObject,
    mut v_inst_1020_: *mut LeanObject,
    mut v_inst_1021_: *mut LeanObject,
    mut v_____do__lift_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: u8 = 0;
    let mut v_toPure_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v_unused_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1032_ = l_Lean_Elab_linter_deprecated_options;
                v___x_1033_ =
                    l_Lean_Option_get___redArg(v___x_1014_, v_____do__lift_1022_, v___x_1032_);
                v___x_1034_ = (lean_unbox(v___x_1033_) as u8);
                lean_dec(v___x_1033_);
                if v___x_1034_ == 0 {
                    lean_dec(v_inst_1021_);
                    lean_dec(v_inst_1020_);
                    lean_dec_ref(v_inst_1019_);
                    lean_dec_ref(v_inst_1018_);
                    lean_dec(v_optionName_1017_);
                    lean_dec_ref(v_decl_1016_);
                    v_toPure_1035_ = lean_ctor_get(v_toApplicative_1015_, 1);
                    lean_inc(v_toPure_1035_);
                    lean_dec_ref(v_toApplicative_1015_);
                    v___x_1036_ = lean_box(0);
                    v___x_1037_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1036_);
                    return v___x_1037_;
                } else {
                    v_deprecation_x3f_1038_ = lean_ctor_get(v_decl_1016_, 4);
                    lean_inc(v_deprecation_x3f_1038_);
                    lean_dec_ref(v_decl_1016_);
                    if lean_obj_tag(v_deprecation_x3f_1038_) == 1 {
                        lean_dec_ref(v_toApplicative_1015_);
                        v_val_1039_ = lean_ctor_get(v_deprecation_x3f_1038_, 0);
                        lean_inc(v_val_1039_);
                        lean_dec_ref_known(v_deprecation_x3f_1038_, 1);
                        v_text_x3f_1040_ = lean_ctor_get(v_val_1039_, 1);
                        v_isSharedCheck_1051_ = (!lean_is_exclusive(v_val_1039_)) as u8;
                        if v_isSharedCheck_1051_ == 0 {
                            v_unused_1052_ = lean_ctor_get(v_val_1039_, 0);
                            lean_dec(v_unused_1052_);
                            v___x_1042_ = v_val_1039_;
                            v_isShared_1043_ = v_isSharedCheck_1051_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_text_x3f_1040_);
                            lean_dec(v_val_1039_);
                            v___x_1042_ = lean_box(0);
                            v_isShared_1043_ = v_isSharedCheck_1051_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_deprecation_x3f_1038_);
                        lean_dec(v_inst_1021_);
                        lean_dec(v_inst_1020_);
                        lean_dec_ref(v_inst_1019_);
                        lean_dec_ref(v_inst_1018_);
                        lean_dec(v_optionName_1017_);
                        v_toPure_1053_ = lean_ctor_get(v_toApplicative_1015_, 1);
                        lean_inc(v_toPure_1053_);
                        lean_dec_ref(v_toApplicative_1015_);
                        v___x_1054_ = lean_box(0);
                        v___x_1055_ = lean_apply_2(v_toPure_1053_, lean_box(0), v___x_1054_);
                        return v___x_1055_;
                    }
                }
            }
            1 => {
                v___x_1025_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4,
                );
                v___x_1026_ = l_Lean_MessageData_ofName(v_optionName_1017_);
                v___x_1027_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1027_, 0, v___x_1025_);
                lean_ctor_set(v___x_1027_, 1, v___x_1026_);
                v___x_1028_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__1,
                );
                v___x_1029_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1029_, 0, v___x_1027_);
                lean_ctor_set(v___x_1029_, 1, v___x_1028_);
                v___x_1030_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1030_, 0, v___x_1029_);
                lean_ctor_set(v___x_1030_, 1, v___y_1024_);
                v___x_1031_ = l_Lean_logWarning___redArg(
                    v_inst_1018_,
                    v_inst_1019_,
                    v_inst_1020_,
                    v_inst_1021_,
                    v___x_1030_,
                );
                return v___x_1031_;
            }
            2 => {
                if lean_obj_tag(v_text_x3f_1040_) == 0 {
                    lean_del_object(v___x_1042_);
                    v___x_1044_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__3,
                    );
                    v___y_1024_ = v___x_1044_;
                    state = 1;
                    continue;
                } else {
                    v_val_1045_ = lean_ctor_get(v_text_x3f_1040_, 0);
                    lean_inc(v_val_1045_);
                    lean_dec_ref_known(v_text_x3f_1040_, 1);
                    v___x_1046_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___closed__5,
                    );
                    v___x_1047_ = l_Lean_stringToMessageData(v_val_1045_);
                    if v_isShared_1043_ == 0 {
                        lean_ctor_set_tag(v___x_1042_, 7);
                        lean_ctor_set(v___x_1042_, 1, v___x_1047_);
                        lean_ctor_set(v___x_1042_, 0, v___x_1046_);
                        v___x_1049_ = v___x_1042_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1050_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1046_);
                        lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1047_);
                        v___x_1049_ = v_reuseFailAlloc_1050_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___y_1024_ = v___x_1049_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed(
    mut v___x_1056_: *mut LeanObject,
    mut v_toApplicative_1057_: *mut LeanObject,
    mut v_decl_1058_: *mut LeanObject,
    mut v_optionName_1059_: *mut LeanObject,
    mut v_inst_1060_: *mut LeanObject,
    mut v_inst_1061_: *mut LeanObject,
    mut v_inst_1062_: *mut LeanObject,
    mut v_inst_1063_: *mut LeanObject,
    mut v_____do__lift_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1065_: *mut LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Elab_checkDeprecatedOption___redArg___lam__0(
        v___x_1056_,
        v_toApplicative_1057_,
        v_decl_1058_,
        v_optionName_1059_,
        v_inst_1060_,
        v_inst_1061_,
        v_inst_1062_,
        v_inst_1063_,
        v_____do__lift_1064_,
    );
    lean_dec_ref(v_____do__lift_1064_);
    return v_res_1065_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedOption___redArg(
    mut v_inst_1066_: *mut LeanObject,
    mut v_inst_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_inst_1069_: *mut LeanObject,
    mut v_optionName_1070_: *mut LeanObject,
    mut v_decl_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_KVMap_instValueBool;
    v_toApplicative_1073_ = lean_ctor_get(v_inst_1066_, 0);
    lean_inc_ref(v_toApplicative_1073_);
    v_toBind_1074_ = lean_ctor_get(v_inst_1066_, 1);
    lean_inc(v_toBind_1074_);
    lean_inc(v_inst_1067_);
    v___f_1075_ = lean_alloc_closure(
        l_Lean_Elab_checkDeprecatedOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1075_, 0, v___x_1072_);
    lean_closure_set(v___f_1075_, 1, v_toApplicative_1073_);
    lean_closure_set(v___f_1075_, 2, v_decl_1071_);
    lean_closure_set(v___f_1075_, 3, v_optionName_1070_);
    lean_closure_set(v___f_1075_, 4, v_inst_1066_);
    lean_closure_set(v___f_1075_, 5, v_inst_1068_);
    lean_closure_set(v___f_1075_, 6, v_inst_1069_);
    lean_closure_set(v___f_1075_, 7, v_inst_1067_);
    v___x_1076_ = lean_apply_4(
        v_toBind_1074_,
        lean_box(0),
        lean_box(0),
        v_inst_1067_,
        v___f_1075_,
    );
    return v___x_1076_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedOption(
    mut v_m_1077_: *mut LeanObject,
    mut v_inst_1078_: *mut LeanObject,
    mut v_inst_1079_: *mut LeanObject,
    mut v_inst_1080_: *mut LeanObject,
    mut v_inst_1081_: *mut LeanObject,
    mut v_optionName_1082_: *mut LeanObject,
    mut v_decl_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Elab_checkDeprecatedOption___redArg(
        v_inst_1078_,
        v_inst_1079_,
        v_inst_1080_,
        v_inst_1081_,
        v_optionName_1082_,
        v_decl_1083_,
    );
    return v___x_1084_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_SetOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_SetOption_0__Lean_Elab_initFn_00___x40_Lean_Elab_SetOption_1989029226____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_linter_deprecated_options = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_linter_deprecated_options);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_SetOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_SetOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SetOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_SetOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_SetOption(builtin);
}
