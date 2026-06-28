// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.Do Init.System.IOError Init.System.FilePath Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.Ord.Basic Init.Data.String.Basic Init.Data.List.MapIdx Init.Data.Ord.UInt Init.Data.ToString.Macro Init.Data.List.Impl Init.Data.Int.Repr
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{l_ByteArray_extract, l_ByteArray_isEmpty};
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go,
    runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::List::MapIdx::{
    initialize_Init_Data_List_MapIdx, runtime_initialize_Init_Data_List_MapIdx,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, l_String_Slice_Pos_get_x3f,
    runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prev_x3f, l_String_Slice_Pos_prevn,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringString___lam__0___boxed;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_MonadExcept_orElse, l_String_toRawSubstring_x27,
    l_instMonadExceptOfMonadExceptOf___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, l_System_FilePath_join, l_System_FilePath_parent,
    runtime_initialize_Init_System_FilePath,
};
use crate::r#gen::Init::System::IOError::{
    initialize_Init_System_IOError, lean_io_error_to_string, lean_mk_io_user_error,
    runtime_initialize_Init_System_IOError,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::lean_imports_rs::Init::Core::{lean_task_get_own, lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::{
    lean_byte_array_copy_slice, lean_byte_array_fget, lean_byte_array_get,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_validate_utf8,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{lean_string_length, lean_string_push};
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint32_lor, lean_uint32_shift_left, lean_uint64_to_usize,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_byte_array_size,
    lean_mk_empty_array_with_capacity, lean_mk_empty_byte_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_from_utf8_unchecked, lean_string_utf8_byte_size,
    lean_uint8_dec_eq, lean_uint32_dec_eq, lean_uint32_dec_lt, lean_uint32_of_nat,
    lean_uint32_to_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_dbg_sleep;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_uint32, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint32, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint32_once, lean_unbox, lean_unbox_uint32, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static mut l_IO_RealWorld_nonemptyType: *mut LeanObject = core::ptr::null_mut();
pub static l_instMonadBaseIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__1_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadBaseIO___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadBaseIO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__2_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__5___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__3_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__7___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__4_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__9___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__5_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__11___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__6_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadBaseIO___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_instMonadBaseIO___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__7_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__8_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadBaseIO___aux__13___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadBaseIO___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__8_value) as *mut LeanObject;
pub static l_instMonadBaseIO___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadBaseIO___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadBaseIO___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_instMonadBaseIO___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__9_value) as *mut LeanObject;
pub static mut l_instMonadBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadBaseIO___closed__9_value) as *mut LeanObject;
pub static l_instMonadFinallyBaseIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadFinallyBaseIO___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadFinallyBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadFinallyBaseIO___closed__0_value) as *mut LeanObject;
pub static mut l_instMonadFinallyBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadFinallyBaseIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadAttachBaseIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadAttachBaseIO___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadAttachBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachBaseIO___closed__0_value) as *mut LeanObject;
pub static mut l_instMonadAttachBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachBaseIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadLiftBaseIOEIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftBaseIOEIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadLiftBaseIOEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadLiftBaseIOEIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__1_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadEIO___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadEIO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__2_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__3_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__3_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__4_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__7___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__4_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__5_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__9___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__5_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__6_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__11___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__6_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadEIO___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_instMonadEIO___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__7_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__8_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadEIO___aux__13___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadEIO___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__8_value) as *mut LeanObject;
pub static l_instMonadEIO___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadEIO___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadEIO___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_instMonadEIO___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadEIO___closed__9_value) as *mut LeanObject;
pub static l_instMonadFinallyEIO___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadFinallyEIO___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadFinallyEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadFinallyEIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadAttachEIO___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadAttachEIO___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadAttachEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachEIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadExceptOfEIO___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadExceptOfEIO___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadExceptOfEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEIO___closed__0_value) as *mut LeanObject;
pub static l_instMonadExceptOfEIO___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadExceptOfEIO___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadExceptOfEIO___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEIO___closed__1_value) as *mut LeanObject;
pub static l_instMonadExceptOfEIO___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadExceptOfEIO___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadExceptOfEIO___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadExceptOfEIO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfEIO___closed__2_value) as *mut LeanObject;
static mut l_instOrElseEIO___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instOrElseEIO___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_instOrElseEIO___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instOrElseEIO___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_instOrElseEIO___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instOrElseEIO___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_instInhabitedTaskState_default: u8 = 0;
pub static mut l_IO_instInhabitedTaskState: u8 = 0;
pub static l_IO_instReprTaskState_repr___closed__0_value: LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        73, 79, 46, 84, 97, 115, 107, 83, 116, 97, 116, 101, 46, 119, 97, 105, 116, 105, 110, 103,
        0,
    ],
};
static mut l_IO_instReprTaskState_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__0_value) as *mut LeanObject;
pub static l_IO_instReprTaskState_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__0_value) as *mut LeanObject],
};
static mut l_IO_instReprTaskState_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__1_value) as *mut LeanObject;
pub static l_IO_instReprTaskState_repr___closed__2_value: LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        73, 79, 46, 84, 97, 115, 107, 83, 116, 97, 116, 101, 46, 114, 117, 110, 110, 105, 110, 103,
        0,
    ],
};
static mut l_IO_instReprTaskState_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__2_value) as *mut LeanObject;
pub static l_IO_instReprTaskState_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__2_value) as *mut LeanObject],
};
static mut l_IO_instReprTaskState_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__3_value) as *mut LeanObject;
pub static l_IO_instReprTaskState_repr___closed__4_value: LeanStringObject<22> = LeanStringObject {
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
        73, 79, 46, 84, 97, 115, 107, 83, 116, 97, 116, 101, 46, 102, 105, 110, 105, 115, 104, 101,
        100, 0,
    ],
};
static mut l_IO_instReprTaskState_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__4_value) as *mut LeanObject;
pub static l_IO_instReprTaskState_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__4_value) as *mut LeanObject],
};
static mut l_IO_instReprTaskState_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState_repr___closed__5_value) as *mut LeanObject;
static mut l_IO_instReprTaskState_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_instReprTaskState_repr___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_instReprTaskState_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_instReprTaskState_repr___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_instReprTaskState___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instReprTaskState_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_instReprTaskState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instReprTaskState: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instReprTaskState___closed__0_value) as *mut LeanObject;
pub static l_IO_instOrdTaskState___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instOrdTaskState_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_instOrdTaskState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instOrdTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instOrdTaskState: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instOrdTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instLTTaskState: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_instLETaskState: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_instMinTaskState___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instMinTaskState___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_instMinTaskState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMinTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instMinTaskState: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMinTaskState___closed__0_value) as *mut LeanObject;
pub static l_IO_instMaxTaskState___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instMaxTaskState___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_instMaxTaskState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMaxTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instMaxTaskState: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMaxTaskState___closed__0_value) as *mut LeanObject;
pub static l_IO_TaskState_toString___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [119, 97, 105, 116, 105, 110, 103, 0],
};
static mut l_IO_TaskState_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_TaskState_toString___closed__0_value) as *mut LeanObject;
pub static l_IO_TaskState_toString___closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 117, 110, 110, 105, 110, 103, 0],
};
static mut l_IO_TaskState_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_TaskState_toString___closed__1_value) as *mut LeanObject;
pub static l_IO_TaskState_toString___closed__2_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 105, 110, 105, 115, 104, 101, 100, 0],
};
static mut l_IO_TaskState_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_TaskState_toString___closed__2_value) as *mut LeanObject;
pub static l_IO_instToStringTaskState___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_TaskState_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_instToStringTaskState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instToStringTaskState___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instToStringTaskState: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instToStringTaskState___closed__0_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_IO_waitAny___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_IO_waitAny___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_IO_waitAny___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__2_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_IO_waitAny___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__3_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__4_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_IO_waitAny___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__5_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_IO_waitAny___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__6_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__7_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_IO_waitAny___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__8_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__9_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_IO_waitAny___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__10_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__11_value) as *mut LeanObject;
static mut l_IO_waitAny___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_waitAny___auto__1___closed__14_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_IO_waitAny___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__15_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_IO_waitAny___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__15_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__16_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__16_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__16_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__15_value) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__16_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__17_value: LeanStringObject<17> = LeanStringObject {
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
        78, 97, 116, 46, 122, 101, 114, 111, 95, 108, 116, 95, 115, 117, 99, 99, 0,
    ],
};
static mut l_IO_waitAny___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__17_value) as *mut LeanObject;
static mut l_IO_waitAny___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_waitAny___auto__1___closed__20_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_IO_waitAny___auto__1___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__20_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__21_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [122, 101, 114, 111, 95, 108, 116, 95, 115, 117, 99, 99, 0],
};
static mut l_IO_waitAny___auto__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__21_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__20_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__22_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__21_value) as *mut LeanObject,
        3679434288154086795 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__22_value) as *mut LeanObject;
static mut l_IO_waitAny___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_waitAny___auto__1___closed__25_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 108, 101, 0],
};
static mut l_IO_waitAny___auto__1___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__25_value) as *mut LeanObject;
static l_IO_waitAny___auto__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__26_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_IO_waitAny___auto__1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__26_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_IO_waitAny___auto__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__26_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__25_value) as *mut LeanObject,
        3984140175429830279 as *mut LeanObject,
    ],
};
static mut l_IO_waitAny___auto__1___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__26_value) as *mut LeanObject;
pub static l_IO_waitAny___auto__1___closed__27_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_IO_waitAny___auto__1___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__27_value) as *mut LeanObject;
static mut l_IO_waitAny___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__32: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__33: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__34: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__35: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__36: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__37: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__39: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__40_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__40: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__41: *mut LeanObject = core::ptr::null_mut();
static mut l_IO_waitAny___auto__1___closed__42_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_waitAny___auto__1___closed__42: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_waitAny___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_waitAny_x27___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_waitAny_x27___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_IO_waitAny_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_waitAny_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_IO_FS_instInhabitedStream_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instInhabitedStream_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_instInhabitedStream_default___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_instInhabitedStream_default___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_instInhabitedStream_default___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__2_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_instInhabitedStream_default___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__3_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_instInhabitedStream_default___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__4_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_IO_FS_instInhabitedStream_default___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__5_value) as *mut LeanObject;
pub static l_IO_FS_instInhabitedStream_default___closed__6_value: LeanCtorObject<6> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instInhabitedStream_default___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__6_value) as *mut LeanObject;
pub static mut l_IO_FS_instInhabitedStream_default: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__6_value) as *mut LeanObject;
pub static mut l_IO_FS_instInhabitedStream: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instInhabitedStream_default___closed__6_value) as *mut LeanObject;
pub static l_IO_FS_Handle_readToEnd___closed__0_value: LeanStringObject<53> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        84, 114, 105, 101, 100, 32, 116, 111, 32, 114, 101, 97, 100, 32, 102, 114, 111, 109, 32,
        104, 97, 110, 100, 108, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 110,
        111, 110, 32, 85, 84, 70, 45, 56, 32, 100, 97, 116, 97, 46, 0,
    ],
};
static mut l_IO_FS_Handle_readToEnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Handle_readToEnd___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Handle_readToEnd___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(l_IO_FS_Handle_readToEnd___closed__0_value) as *mut LeanObject],
};
static mut l_IO_FS_Handle_readToEnd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Handle_readToEnd___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_Handle_lines___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_IO_FS_Handle_lines___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Handle_lines___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [114, 111, 111, 116, 0],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [102, 105, 108, 101, 78, 97, 109, 101, 0],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprDirEntry_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprDirEntry___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instReprDirEntry_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instReprDirEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instReprDirEntry: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprDirEntry___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            73, 79, 46, 70, 83, 46, 70, 105, 108, 101, 84, 121, 112, 101, 46, 100, 105, 114, 0,
        ],
    };
static mut l_IO_FS_instReprFileType_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_IO_FS_instReprFileType_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            73, 79, 46, 70, 83, 46, 70, 105, 108, 101, 84, 121, 112, 101, 46, 102, 105, 108, 101, 0,
        ],
    };
static mut l_IO_FS_instReprFileType_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__2_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_IO_FS_instReprFileType_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__3_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__4_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            73, 79, 46, 70, 83, 46, 70, 105, 108, 101, 84, 121, 112, 101, 46, 115, 121, 109, 108,
            105, 110, 107, 0,
        ],
    };
static mut l_IO_FS_instReprFileType_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__4_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_IO_FS_instReprFileType_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__5_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__6_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            73, 79, 46, 70, 83, 46, 70, 105, 108, 101, 84, 121, 112, 101, 46, 111, 116, 104, 101,
            114, 0,
        ],
    };
static mut l_IO_FS_instReprFileType_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__6_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_IO_FS_instReprFileType_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType_repr___closed__7_value) as *mut LeanObject;
pub static l_IO_FS_instReprFileType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instReprFileType_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instReprFileType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instReprFileType: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprFileType___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instBEqFileType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instBEqFileType_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instBEqFileType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instBEqFileType___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instBEqFileType: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instBEqFileType___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 101, 99, 0],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 115, 101, 99, 0],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instReprSystemTime_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_FS_instReprSystemTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instReprSystemTime_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instReprSystemTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instReprSystemTime: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprSystemTime___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instBEqSystemTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instBEqSystemTime_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instBEqSystemTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instBEqSystemTime___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instBEqSystemTime: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instBEqSystemTime___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_instOrdSystemTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instOrdSystemTime_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instOrdSystemTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instOrdSystemTime___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instOrdSystemTime: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instOrdSystemTime___closed__0_value) as *mut LeanObject;
static mut l_IO_FS_instInhabitedSystemTime_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instInhabitedSystemTime_default___closed__0: u32 = 0;
static mut l_IO_FS_instInhabitedSystemTime_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_instInhabitedSystemTime_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_IO_FS_instInhabitedSystemTime_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_FS_instInhabitedSystemTime: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_FS_instLTSystemTime: *mut LeanObject = core::ptr::null_mut();
pub static mut l_IO_FS_instLESystemTime: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [97, 99, 99, 101, 115, 115, 101, 100, 0],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__4_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [109, 111, 100, 105, 102, 105, 101, 100, 0],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__6_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [98, 121, 116, 101, 83, 105, 122, 101, 0],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 121, 112, 101, 0],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__10_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [110, 117, 109, 76, 105, 110, 107, 115, 0],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_IO_FS_instReprMetadata_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_IO_FS_instReprMetadata___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_instReprMetadata_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_FS_instReprMetadata___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata___closed__0_value) as *mut LeanObject;
pub static mut l_IO_FS_instReprMetadata: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_instReprMetadata___closed__0_value) as *mut LeanObject;
static mut l_IO_FS_readBinFile___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_readBinFile___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_IO_FS_readFile___closed__0_value: LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        84, 114, 105, 101, 100, 32, 116, 111, 32, 114, 101, 97, 100, 32, 102, 105, 108, 101, 32,
        39, 0,
    ],
};
static mut l_IO_FS_readFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_readFile___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_readFile___closed__1_value: LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        39, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 110, 111, 110, 32, 85, 84, 70,
        45, 56, 32, 100, 97, 116, 97, 46, 0,
    ],
};
static mut l_IO_FS_readFile___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_readFile___closed__1_value) as *mut LeanObject;
pub static l_IO_withStdin___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_withStdin___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_withStdin___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_withStdin___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_println___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_println___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_println___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_appDir___closed__0_value: LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        73, 79, 46, 97, 112, 112, 68, 105, 114, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101,
        100, 32, 102, 105, 108, 101, 110, 97, 109, 101, 32, 39, 0,
    ],
};
static mut l_IO_appDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_appDir___closed__0_value) as *mut LeanObject;
pub static l_IO_appDir___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_IO_appDir___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_appDir___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_withTempFile___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_createTempFile___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_withTempFile___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withTempFile___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_withTempDir___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_FS_createTempDir___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_FS_withTempDir___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withTempDir___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_Process_output___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [2 as *mut LeanObject],
};
static mut l_IO_Process_output___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Process_output___closed__0_value) as *mut LeanObject;
pub static l_IO_Process_output___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l_IO_Process_output___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Process_output___closed__1_value) as *mut LeanObject;
pub static l_IO_Process_run___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 114, 111, 99, 101, 115, 115, 32, 39, 0],
};
static mut l_IO_Process_run___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Process_run___closed__0_value) as *mut LeanObject;
pub static l_IO_Process_run___closed__1_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        39, 32, 101, 120, 105, 116, 101, 100, 32, 119, 105, 116, 104, 32, 99, 111, 100, 101, 32, 0,
    ],
};
static mut l_IO_Process_run___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Process_run___closed__1_value) as *mut LeanObject;
pub static l_IO_Process_run___closed__2_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [10, 115, 116, 100, 101, 114, 114, 58, 10, 0],
};
static mut l_IO_Process_run___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Process_run___closed__2_value) as *mut LeanObject;
pub static l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_instMonadLiftSTRealWorldBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value) as *mut LeanObject;
pub static mut l_IO_instMonadLiftSTRealWorldBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 0],
    };
static mut l_IO_FS_Stream_ofBuffer___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_IO_FS_Stream_ofBuffer___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_Stream_ofBuffer___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_FS_Stream_ofBuffer___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_IO_FS_Stream_ofBuffer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_ofBuffer___closed__0_value) as *mut LeanObject;
pub static l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(1024 as *mut LeanObject)] };
pub static mut l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readToEnd___closed__0_value: LeanStringObject<53> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        84, 114, 105, 101, 100, 32, 116, 111, 32, 114, 101, 97, 100, 32, 102, 114, 111, 109, 32,
        115, 116, 114, 101, 97, 109, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 110,
        111, 110, 32, 85, 84, 70, 45, 56, 32, 100, 97, 116, 97, 46, 0,
    ],
};
static mut l_IO_FS_Stream_readToEnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readToEnd___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readToEnd___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(l_IO_FS_Stream_readToEnd___closed__0_value) as *mut LeanObject],
};
static mut l_IO_FS_Stream_readToEnd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readToEnd___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value: LeanStringObject<17> =
    LeanStringObject {
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
            83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0,
        ],
    };
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value)
        as *mut LeanObject;
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_withIsolatedStreams___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_withIsolatedStreams___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_IO_FS_withIsolatedStreams___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_withIsolatedStreams___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_termPrintln_x21_____00__closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 101, 114, 109, 80, 114, 105, 110, 116, 108, 110, 33, 95, 95, 0,
    ],
};
static mut l_termPrintln_x21_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__0_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__0_value) as *mut LeanObject,
        682939661955135997 as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__1_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_termPrintln_x21_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__2_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__3_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__4_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 114, 105, 110, 116, 108, 110, 33, 32, 0],
};
static mut l_termPrintln_x21_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__4_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_termPrintln_x21_____00__closed__4_value) as *mut LeanObject],
};
static mut l_termPrintln_x21_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__5_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__6_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 114, 101, 108, 115, 101, 0],
};
static mut l_termPrintln_x21_____00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__6_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__6_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__7_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__8_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_termPrintln_x21_____00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__8_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__8_value) as *mut LeanObject,
        18163029821153688220 as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__9_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__10_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_termPrintln_x21_____00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__10_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__10_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__11_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__11_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__12_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__12_value) as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__13_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__12_value) as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__14_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__14_value) as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__15_value) as *mut LeanObject;
pub static l_termPrintln_x21_____00__closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_termPrintln_x21_____00__closed__15_value) as *mut LeanObject,
    ],
};
static mut l_termPrintln_x21_____00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__16_value) as *mut LeanObject;
pub static mut l_termPrintln_x21____: *mut LeanObject =
    core::ptr::addr_of!(l_termPrintln_x21_____00__closed__16_value) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100,
        0,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value
        ) as *mut LeanObject,
        14298422259736409839 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value
) as *mut LeanObject;
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value
) as *mut LeanObject;
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value
) as *mut LeanObject;
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value:
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
    m_data: [83, 121, 115, 116, 101, 109, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value
        ) as *mut LeanObject,
        3794196532276496372 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value:
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
    m_data: [73, 79, 46, 112, 114, 105, 110, 116, 108, 110, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value
) as *mut LeanObject;
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [73, 79, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value:
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
    m_data: [112, 114, 105, 110, 116, 108, 110, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value
) as *mut LeanObject;
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value) as *mut LeanObject,4390522573605260290 as *mut LeanObject] };
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value) as *mut LeanObject,1423516185670340977 as *mut LeanObject] };
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value
) as *mut LeanObject;
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value
        ) as *mut LeanObject,
        4390522573605260290 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value:
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
    m_data: [85, 110, 105, 116, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value
) as *mut LeanObject;
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value
        ) as *mut LeanObject,
        9833841078580172006 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value
) as *mut LeanObject;
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_IO_waitAny___auto__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value:
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
    m_data: [116, 101, 114, 109, 83, 33, 95, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value:
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
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value
        ) as *mut LeanObject,
        11081549158230622750 as *mut LeanObject,
    ],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value
) as *mut LeanObject;
pub static l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [115, 33, 0],
};
static mut l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value
) as *mut LeanObject;
pub unsafe fn _init_l_IO_RealWorld_nonemptyType() -> *mut LeanObject {
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    v___x_5475_ = lean_box(0);
    return v___x_5475_;
}
pub unsafe fn l_instMonadBaseIO___aux__1___redArg(
    mut v_f_5476_: *mut LeanObject,
    mut v_x_5477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    v___x_5479_ = lean_apply_1(v_x_5477_, lean_box(0));
    v___x_5480_ = lean_apply_1(v_f_5476_, v___x_5479_);
    return v___x_5480_;
}
pub unsafe fn l_instMonadBaseIO___aux__1___redArg___boxed(
    mut v_f_5481_: *mut LeanObject,
    mut v_x_5482_: *mut LeanObject,
    mut v_a_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5484_: *mut LeanObject = core::ptr::null_mut();
    v_res_5484_ = l_instMonadBaseIO___aux__1___redArg(v_f_5481_, v_x_5482_);
    return v_res_5484_;
}
pub unsafe fn l_instMonadBaseIO___aux__1(
    mut v_00_u03b1_5485_: *mut LeanObject,
    mut v_00_u03b2_5486_: *mut LeanObject,
    mut v_f_5487_: *mut LeanObject,
    mut v_x_5488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    v___x_5490_ = lean_apply_1(v_x_5488_, lean_box(0));
    v___x_5491_ = lean_apply_1(v_f_5487_, v___x_5490_);
    return v___x_5491_;
}
pub unsafe fn l_instMonadBaseIO___aux__1___boxed(
    mut v_00_u03b1_5492_: *mut LeanObject,
    mut v_00_u03b2_5493_: *mut LeanObject,
    mut v_f_5494_: *mut LeanObject,
    mut v_x_5495_: *mut LeanObject,
    mut v_a_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5497_: *mut LeanObject = core::ptr::null_mut();
    v_res_5497_ =
        l_instMonadBaseIO___aux__1(v_00_u03b1_5492_, v_00_u03b2_5493_, v_f_5494_, v_x_5495_);
    return v_res_5497_;
}
pub unsafe fn l_instMonadBaseIO___aux__3___redArg(
    mut v_a_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    v___x_5501_ = lean_apply_1(v_a_5499_, lean_box(0));
    lean_dec(v___x_5501_);
    lean_inc(v_a_5498_);
    return v_a_5498_;
}
pub unsafe fn l_instMonadBaseIO___aux__3___redArg___boxed(
    mut v_a_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5505_: *mut LeanObject = core::ptr::null_mut();
    v_res_5505_ = l_instMonadBaseIO___aux__3___redArg(v_a_5502_, v_a_5503_);
    lean_dec(v_a_5502_);
    return v_res_5505_;
}
pub unsafe fn l_instMonadBaseIO___aux__3(
    mut v_00_u03b1_5506_: *mut LeanObject,
    mut v_00_u03b2_5507_: *mut LeanObject,
    mut v_a_5508_: *mut LeanObject,
    mut v_a_5509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    v___x_5511_ = lean_apply_1(v_a_5509_, lean_box(0));
    lean_dec(v___x_5511_);
    lean_inc(v_a_5508_);
    return v_a_5508_;
}
pub unsafe fn l_instMonadBaseIO___aux__3___boxed(
    mut v_00_u03b1_5512_: *mut LeanObject,
    mut v_00_u03b2_5513_: *mut LeanObject,
    mut v_a_5514_: *mut LeanObject,
    mut v_a_5515_: *mut LeanObject,
    mut v_a_5516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5517_: *mut LeanObject = core::ptr::null_mut();
    v_res_5517_ =
        l_instMonadBaseIO___aux__3(v_00_u03b1_5512_, v_00_u03b2_5513_, v_a_5514_, v_a_5515_);
    lean_dec(v_a_5514_);
    return v_res_5517_;
}
pub unsafe fn l_instMonadBaseIO___aux__5___redArg(
    mut v_x_5518_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_5518_);
    return v_x_5518_;
}
pub unsafe fn l_instMonadBaseIO___aux__5___redArg___boxed(
    mut v_x_5520_: *mut LeanObject,
    mut v_a_5521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5522_: *mut LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_instMonadBaseIO___aux__5___redArg(v_x_5520_);
    lean_dec(v_x_5520_);
    return v_res_5522_;
}
pub unsafe fn l_instMonadBaseIO___aux__5(
    mut v_00_u03b1_5523_: *mut LeanObject,
    mut v_x_5524_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_5524_);
    return v_x_5524_;
}
pub unsafe fn l_instMonadBaseIO___aux__5___boxed(
    mut v_00_u03b1_5526_: *mut LeanObject,
    mut v_x_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5529_: *mut LeanObject = core::ptr::null_mut();
    v_res_5529_ = l_instMonadBaseIO___aux__5(v_00_u03b1_5526_, v_x_5527_);
    lean_dec(v_x_5527_);
    return v_res_5529_;
}
pub unsafe fn l_instMonadBaseIO___aux__7___redArg(
    mut v_f_5530_: *mut LeanObject,
    mut v_x_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    v___x_5533_ = lean_apply_1(v_f_5530_, lean_box(0));
    v___x_5534_ = lean_box(0);
    v___x_5535_ = lean_apply_2(v_x_5531_, v___x_5534_, lean_box(0));
    v___x_5536_ = lean_apply_1(v___x_5533_, v___x_5535_);
    return v___x_5536_;
}
pub unsafe fn l_instMonadBaseIO___aux__7___redArg___boxed(
    mut v_f_5537_: *mut LeanObject,
    mut v_x_5538_: *mut LeanObject,
    mut v_a_5539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5540_: *mut LeanObject = core::ptr::null_mut();
    v_res_5540_ = l_instMonadBaseIO___aux__7___redArg(v_f_5537_, v_x_5538_);
    return v_res_5540_;
}
pub unsafe fn l_instMonadBaseIO___aux__7(
    mut v_00_u03b1_5541_: *mut LeanObject,
    mut v_00_u03b2_5542_: *mut LeanObject,
    mut v_f_5543_: *mut LeanObject,
    mut v_x_5544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    v___x_5546_ = lean_apply_1(v_f_5543_, lean_box(0));
    v___x_5547_ = lean_box(0);
    v___x_5548_ = lean_apply_2(v_x_5544_, v___x_5547_, lean_box(0));
    v___x_5549_ = lean_apply_1(v___x_5546_, v___x_5548_);
    return v___x_5549_;
}
pub unsafe fn l_instMonadBaseIO___aux__7___boxed(
    mut v_00_u03b1_5550_: *mut LeanObject,
    mut v_00_u03b2_5551_: *mut LeanObject,
    mut v_f_5552_: *mut LeanObject,
    mut v_x_5553_: *mut LeanObject,
    mut v_a_5554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5555_: *mut LeanObject = core::ptr::null_mut();
    v_res_5555_ =
        l_instMonadBaseIO___aux__7(v_00_u03b1_5550_, v_00_u03b2_5551_, v_f_5552_, v_x_5553_);
    return v_res_5555_;
}
pub unsafe fn l_instMonadBaseIO___aux__9___redArg(
    mut v_x_5556_: *mut LeanObject,
    mut v_y_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    v___x_5559_ = lean_apply_1(v_x_5556_, lean_box(0));
    v___x_5560_ = lean_box(0);
    v___x_5561_ = lean_apply_2(v_y_5557_, v___x_5560_, lean_box(0));
    lean_dec(v___x_5561_);
    return v___x_5559_;
}
pub unsafe fn l_instMonadBaseIO___aux__9___redArg___boxed(
    mut v_x_5562_: *mut LeanObject,
    mut v_y_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5565_: *mut LeanObject = core::ptr::null_mut();
    v_res_5565_ = l_instMonadBaseIO___aux__9___redArg(v_x_5562_, v_y_5563_);
    return v_res_5565_;
}
pub unsafe fn l_instMonadBaseIO___aux__9(
    mut v_00_u03b1_5566_: *mut LeanObject,
    mut v_00_u03b2_5567_: *mut LeanObject,
    mut v_x_5568_: *mut LeanObject,
    mut v_y_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    v___x_5571_ = lean_apply_1(v_x_5568_, lean_box(0));
    v___x_5572_ = lean_box(0);
    v___x_5573_ = lean_apply_2(v_y_5569_, v___x_5572_, lean_box(0));
    lean_dec(v___x_5573_);
    return v___x_5571_;
}
pub unsafe fn l_instMonadBaseIO___aux__9___boxed(
    mut v_00_u03b1_5574_: *mut LeanObject,
    mut v_00_u03b2_5575_: *mut LeanObject,
    mut v_x_5576_: *mut LeanObject,
    mut v_y_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5579_: *mut LeanObject = core::ptr::null_mut();
    v_res_5579_ =
        l_instMonadBaseIO___aux__9(v_00_u03b1_5574_, v_00_u03b2_5575_, v_x_5576_, v_y_5577_);
    return v_res_5579_;
}
pub unsafe fn l_instMonadBaseIO___aux__11___redArg(
    mut v_x_5580_: *mut LeanObject,
    mut v_y_5581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    v___x_5583_ = lean_apply_1(v_x_5580_, lean_box(0));
    lean_dec(v___x_5583_);
    v___x_5584_ = lean_box(0);
    v___x_5585_ = lean_apply_2(v_y_5581_, v___x_5584_, lean_box(0));
    return v___x_5585_;
}
pub unsafe fn l_instMonadBaseIO___aux__11___redArg___boxed(
    mut v_x_5586_: *mut LeanObject,
    mut v_y_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5589_: *mut LeanObject = core::ptr::null_mut();
    v_res_5589_ = l_instMonadBaseIO___aux__11___redArg(v_x_5586_, v_y_5587_);
    return v_res_5589_;
}
pub unsafe fn l_instMonadBaseIO___aux__11(
    mut v_00_u03b1_5590_: *mut LeanObject,
    mut v_00_u03b2_5591_: *mut LeanObject,
    mut v_x_5592_: *mut LeanObject,
    mut v_y_5593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    v___x_5595_ = lean_apply_1(v_x_5592_, lean_box(0));
    lean_dec(v___x_5595_);
    v___x_5596_ = lean_box(0);
    v___x_5597_ = lean_apply_2(v_y_5593_, v___x_5596_, lean_box(0));
    return v___x_5597_;
}
pub unsafe fn l_instMonadBaseIO___aux__11___boxed(
    mut v_00_u03b1_5598_: *mut LeanObject,
    mut v_00_u03b2_5599_: *mut LeanObject,
    mut v_x_5600_: *mut LeanObject,
    mut v_y_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5603_: *mut LeanObject = core::ptr::null_mut();
    v_res_5603_ =
        l_instMonadBaseIO___aux__11(v_00_u03b1_5598_, v_00_u03b2_5599_, v_x_5600_, v_y_5601_);
    return v_res_5603_;
}
pub unsafe fn l_instMonadBaseIO___aux__13___redArg(
    mut v_x_5604_: *mut LeanObject,
    mut v_f_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    v___x_5607_ = lean_apply_1(v_x_5604_, lean_box(0));
    v___x_5608_ = lean_apply_2(v_f_5605_, v___x_5607_, lean_box(0));
    return v___x_5608_;
}
pub unsafe fn l_instMonadBaseIO___aux__13___redArg___boxed(
    mut v_x_5609_: *mut LeanObject,
    mut v_f_5610_: *mut LeanObject,
    mut v_a_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5612_: *mut LeanObject = core::ptr::null_mut();
    v_res_5612_ = l_instMonadBaseIO___aux__13___redArg(v_x_5609_, v_f_5610_);
    return v_res_5612_;
}
pub unsafe fn l_instMonadBaseIO___aux__13(
    mut v_00_u03b1_5613_: *mut LeanObject,
    mut v_00_u03b2_5614_: *mut LeanObject,
    mut v_x_5615_: *mut LeanObject,
    mut v_f_5616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    v___x_5618_ = lean_apply_1(v_x_5615_, lean_box(0));
    v___x_5619_ = lean_apply_2(v_f_5616_, v___x_5618_, lean_box(0));
    return v___x_5619_;
}
pub unsafe fn l_instMonadBaseIO___aux__13___boxed(
    mut v_00_u03b1_5620_: *mut LeanObject,
    mut v_00_u03b2_5621_: *mut LeanObject,
    mut v_x_5622_: *mut LeanObject,
    mut v_f_5623_: *mut LeanObject,
    mut v_a_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5625_: *mut LeanObject = core::ptr::null_mut();
    v_res_5625_ =
        l_instMonadBaseIO___aux__13(v_00_u03b1_5620_, v_00_u03b2_5621_, v_x_5622_, v_f_5623_);
    return v_res_5625_;
}
pub unsafe fn l_instMonadFinallyBaseIO___aux__1___redArg(
    mut v_x_5646_: *mut LeanObject,
    mut v_f_5647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    v___x_5649_ = lean_apply_1(v_x_5646_, lean_box(0));
    lean_inc(v___x_5649_);
    v___x_5650_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5650_, 0, v___x_5649_);
    v___x_5651_ = lean_apply_2(v_f_5647_, v___x_5650_, lean_box(0));
    v___x_5652_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5652_, 0, v___x_5649_);
    lean_ctor_set(v___x_5652_, 1, v___x_5651_);
    return v___x_5652_;
}
pub unsafe fn l_instMonadFinallyBaseIO___aux__1___redArg___boxed(
    mut v_x_5653_: *mut LeanObject,
    mut v_f_5654_: *mut LeanObject,
    mut v_s_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5656_: *mut LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_instMonadFinallyBaseIO___aux__1___redArg(v_x_5653_, v_f_5654_);
    return v_res_5656_;
}
pub unsafe fn l_instMonadFinallyBaseIO___aux__1(
    mut v_00_u03b1_5657_: *mut LeanObject,
    mut v_00_u03b2_5658_: *mut LeanObject,
    mut v_x_5659_: *mut LeanObject,
    mut v_f_5660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    v___x_5662_ = lean_apply_1(v_x_5659_, lean_box(0));
    lean_inc(v___x_5662_);
    v___x_5663_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5663_, 0, v___x_5662_);
    v___x_5664_ = lean_apply_2(v_f_5660_, v___x_5663_, lean_box(0));
    v___x_5665_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5665_, 0, v___x_5662_);
    lean_ctor_set(v___x_5665_, 1, v___x_5664_);
    return v___x_5665_;
}
pub unsafe fn l_instMonadFinallyBaseIO___aux__1___boxed(
    mut v_00_u03b1_5666_: *mut LeanObject,
    mut v_00_u03b2_5667_: *mut LeanObject,
    mut v_x_5668_: *mut LeanObject,
    mut v_f_5669_: *mut LeanObject,
    mut v_s_5670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5671_: *mut LeanObject = core::ptr::null_mut();
    v_res_5671_ =
        l_instMonadFinallyBaseIO___aux__1(v_00_u03b1_5666_, v_00_u03b2_5667_, v_x_5668_, v_f_5669_);
    return v_res_5671_;
}
pub unsafe fn l_instMonadAttachBaseIO___aux__3___redArg(
    mut v_x_5674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    v___x_5676_ = lean_apply_1(v_x_5674_, lean_box(0));
    return v___x_5676_;
}
pub unsafe fn l_instMonadAttachBaseIO___aux__3___redArg___boxed(
    mut v_x_5677_: *mut LeanObject,
    mut v_s_5678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5679_: *mut LeanObject = core::ptr::null_mut();
    v_res_5679_ = l_instMonadAttachBaseIO___aux__3___redArg(v_x_5677_);
    return v_res_5679_;
}
pub unsafe fn l_instMonadAttachBaseIO___aux__3(
    mut v_00_u03b1_5680_: *mut LeanObject,
    mut v_x_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    v___x_5683_ = lean_apply_1(v_x_5681_, lean_box(0));
    return v___x_5683_;
}
pub unsafe fn l_instMonadAttachBaseIO___aux__3___boxed(
    mut v_00_u03b1_5684_: *mut LeanObject,
    mut v_x_5685_: *mut LeanObject,
    mut v_s_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5687_: *mut LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_instMonadAttachBaseIO___aux__3(v_00_u03b1_5684_, v_x_5685_);
    return v_res_5687_;
}
pub unsafe fn l_BaseIO_map___redArg(
    mut v_f_5690_: *mut LeanObject,
    mut v_x_5691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    v___x_5693_ = lean_apply_1(v_x_5691_, lean_box(0));
    v___x_5694_ = lean_apply_1(v_f_5690_, v___x_5693_);
    return v___x_5694_;
}
pub unsafe fn l_BaseIO_map___redArg___boxed(
    mut v_f_5695_: *mut LeanObject,
    mut v_x_5696_: *mut LeanObject,
    mut v_a_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5698_: *mut LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_BaseIO_map___redArg(v_f_5695_, v_x_5696_);
    return v_res_5698_;
}
pub unsafe fn l_BaseIO_map(
    mut v_00_u03b1_5699_: *mut LeanObject,
    mut v_00_u03b2_5700_: *mut LeanObject,
    mut v_f_5701_: *mut LeanObject,
    mut v_x_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    v___x_5704_ = lean_apply_1(v_x_5702_, lean_box(0));
    v___x_5705_ = lean_apply_1(v_f_5701_, v___x_5704_);
    return v___x_5705_;
}
pub unsafe fn l_BaseIO_map___boxed(
    mut v_00_u03b1_5706_: *mut LeanObject,
    mut v_00_u03b2_5707_: *mut LeanObject,
    mut v_f_5708_: *mut LeanObject,
    mut v_x_5709_: *mut LeanObject,
    mut v_a_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5711_: *mut LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_BaseIO_map(v_00_u03b1_5706_, v_00_u03b2_5707_, v_f_5708_, v_x_5709_);
    return v_res_5711_;
}
pub unsafe fn l_BaseIO_toEIO___redArg(mut v_act_5712_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5714_ = lean_apply_1(v_act_5712_, lean_box(0));
    v___x_5715_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5715_, 0, v___x_5714_);
    return v___x_5715_;
}
pub unsafe fn l_BaseIO_toEIO___redArg___boxed(
    mut v_act_5716_: *mut LeanObject,
    mut v_s_5717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5718_: *mut LeanObject = core::ptr::null_mut();
    v_res_5718_ = l_BaseIO_toEIO___redArg(v_act_5716_);
    return v_res_5718_;
}
pub unsafe fn l_BaseIO_toEIO(
    mut v_00_u03b1_5719_: *mut LeanObject,
    mut v_00_u03b5_5720_: *mut LeanObject,
    mut v_act_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    v___x_5723_ = lean_apply_1(v_act_5721_, lean_box(0));
    v___x_5724_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5724_, 0, v___x_5723_);
    return v___x_5724_;
}
pub unsafe fn l_BaseIO_toEIO___boxed(
    mut v_00_u03b1_5725_: *mut LeanObject,
    mut v_00_u03b5_5726_: *mut LeanObject,
    mut v_act_5727_: *mut LeanObject,
    mut v_s_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    v_res_5729_ = l_BaseIO_toEIO(v_00_u03b1_5725_, v_00_u03b5_5726_, v_act_5727_);
    return v_res_5729_;
}
pub unsafe fn l_instMonadLiftBaseIOEIO___lam__0(
    mut v_00_u03b1_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    v___x_5733_ = lean_apply_1(v___y_5731_, lean_box(0));
    v___x_5734_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5734_, 0, v___x_5733_);
    return v___x_5734_;
}
pub unsafe fn l_instMonadLiftBaseIOEIO___lam__0___boxed(
    mut v_00_u03b1_5735_: *mut LeanObject,
    mut v___y_5736_: *mut LeanObject,
    mut v___y_5737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5738_: *mut LeanObject = core::ptr::null_mut();
    v_res_5738_ = l_instMonadLiftBaseIOEIO___lam__0(v_00_u03b1_5735_, v___y_5736_);
    return v_res_5738_;
}
pub unsafe fn l_instMonadLiftBaseIOEIO(mut v_00_u03b5_5740_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5741_: *mut LeanObject = core::ptr::null_mut();
    v___f_5741_ = l_instMonadLiftBaseIOEIO___closed__0;
    return v___f_5741_;
}
pub unsafe fn l_EIO_toBaseIO___redArg(mut v_act_5742_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5748_: u8 = 0;
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5752_: u8 = 0;
    let mut v_a_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5744_ = lean_apply_1(v_act_5742_, lean_box(0));
                if lean_obj_tag(v___x_5744_) == 0 {
                    v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
                    v_isSharedCheck_5752_ = (!lean_is_exclusive(v___x_5744_)) as u8;
                    if v_isSharedCheck_5752_ == 0 {
                        v___x_5747_ = v___x_5744_;
                        v_isShared_5748_ = v_isSharedCheck_5752_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5745_);
                        lean_dec(v___x_5744_);
                        v___x_5747_ = lean_box(0);
                        v_isShared_5748_ = v_isSharedCheck_5752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5753_ = lean_ctor_get(v___x_5744_, 0);
                    v_isSharedCheck_5760_ = (!lean_is_exclusive(v___x_5744_)) as u8;
                    if v_isSharedCheck_5760_ == 0 {
                        v___x_5755_ = v___x_5744_;
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5753_);
                        lean_dec(v___x_5744_);
                        v___x_5755_ = lean_box(0);
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5748_ == 0 {
                    lean_ctor_set_tag(v___x_5747_, 1);
                    v___x_5750_ = v___x_5747_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
                    v___x_5750_ = v_reuseFailAlloc_5751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5750_;
            }
            3 => {
                if v_isShared_5756_ == 0 {
                    lean_ctor_set_tag(v___x_5755_, 0);
                    v___x_5758_ = v___x_5755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toBaseIO___redArg___boxed(
    mut v_act_5761_: *mut LeanObject,
    mut v_s_5762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5763_: *mut LeanObject = core::ptr::null_mut();
    v_res_5763_ = l_EIO_toBaseIO___redArg(v_act_5761_);
    return v_res_5763_;
}
pub unsafe fn l_EIO_toBaseIO(
    mut v_00_u03b5_5764_: *mut LeanObject,
    mut v_00_u03b1_5765_: *mut LeanObject,
    mut v_act_5766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5772_: u8 = 0;
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5776_: u8 = 0;
    let mut v_a_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5780_: u8 = 0;
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5768_ = lean_apply_1(v_act_5766_, lean_box(0));
                if lean_obj_tag(v___x_5768_) == 0 {
                    v_a_5769_ = lean_ctor_get(v___x_5768_, 0);
                    v_isSharedCheck_5776_ = (!lean_is_exclusive(v___x_5768_)) as u8;
                    if v_isSharedCheck_5776_ == 0 {
                        v___x_5771_ = v___x_5768_;
                        v_isShared_5772_ = v_isSharedCheck_5776_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5769_);
                        lean_dec(v___x_5768_);
                        v___x_5771_ = lean_box(0);
                        v_isShared_5772_ = v_isSharedCheck_5776_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5777_ = lean_ctor_get(v___x_5768_, 0);
                    v_isSharedCheck_5784_ = (!lean_is_exclusive(v___x_5768_)) as u8;
                    if v_isSharedCheck_5784_ == 0 {
                        v___x_5779_ = v___x_5768_;
                        v_isShared_5780_ = v_isSharedCheck_5784_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5777_);
                        lean_dec(v___x_5768_);
                        v___x_5779_ = lean_box(0);
                        v_isShared_5780_ = v_isSharedCheck_5784_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5772_ == 0 {
                    lean_ctor_set_tag(v___x_5771_, 1);
                    v___x_5774_ = v___x_5771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
                    v___x_5774_ = v_reuseFailAlloc_5775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5774_;
            }
            3 => {
                if v_isShared_5780_ == 0 {
                    lean_ctor_set_tag(v___x_5779_, 0);
                    v___x_5782_ = v___x_5779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
                    v___x_5782_ = v_reuseFailAlloc_5783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toBaseIO___boxed(
    mut v_00_u03b5_5785_: *mut LeanObject,
    mut v_00_u03b1_5786_: *mut LeanObject,
    mut v_act_5787_: *mut LeanObject,
    mut v_s_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5789_: *mut LeanObject = core::ptr::null_mut();
    v_res_5789_ = l_EIO_toBaseIO(v_00_u03b5_5785_, v_00_u03b1_5786_, v_act_5787_);
    return v_res_5789_;
}
pub unsafe fn l_EIO_catchExceptions___redArg(
    mut v_act_5790_: *mut LeanObject,
    mut v_h_5791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    v___x_5793_ = lean_apply_1(v_act_5790_, lean_box(0));
    if lean_obj_tag(v___x_5793_) == 0 {
        let mut v_a_5794_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_h_5791_);
        v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
        lean_inc(v_a_5794_);
        lean_dec_ref_known(v___x_5793_, 1);
        return v_a_5794_;
    } else {
        let mut v_a_5795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
        v_a_5795_ = lean_ctor_get(v___x_5793_, 0);
        lean_inc(v_a_5795_);
        lean_dec_ref_known(v___x_5793_, 1);
        v___x_5796_ = lean_apply_2(v_h_5791_, v_a_5795_, lean_box(0));
        return v___x_5796_;
    }
}
pub unsafe fn l_EIO_catchExceptions___redArg___boxed(
    mut v_act_5797_: *mut LeanObject,
    mut v_h_5798_: *mut LeanObject,
    mut v_s_5799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5800_: *mut LeanObject = core::ptr::null_mut();
    v_res_5800_ = l_EIO_catchExceptions___redArg(v_act_5797_, v_h_5798_);
    return v_res_5800_;
}
pub unsafe fn l_EIO_catchExceptions(
    mut v_00_u03b5_5801_: *mut LeanObject,
    mut v_00_u03b1_5802_: *mut LeanObject,
    mut v_act_5803_: *mut LeanObject,
    mut v_h_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    v___x_5806_ = lean_apply_1(v_act_5803_, lean_box(0));
    if lean_obj_tag(v___x_5806_) == 0 {
        let mut v_a_5807_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_h_5804_);
        v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
        lean_inc(v_a_5807_);
        lean_dec_ref_known(v___x_5806_, 1);
        return v_a_5807_;
    } else {
        let mut v_a_5808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
        v_a_5808_ = lean_ctor_get(v___x_5806_, 0);
        lean_inc(v_a_5808_);
        lean_dec_ref_known(v___x_5806_, 1);
        v___x_5809_ = lean_apply_2(v_h_5804_, v_a_5808_, lean_box(0));
        return v___x_5809_;
    }
}
pub unsafe fn l_EIO_catchExceptions___boxed(
    mut v_00_u03b5_5810_: *mut LeanObject,
    mut v_00_u03b1_5811_: *mut LeanObject,
    mut v_act_5812_: *mut LeanObject,
    mut v_h_5813_: *mut LeanObject,
    mut v_s_5814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5815_: *mut LeanObject = core::ptr::null_mut();
    v_res_5815_ = l_EIO_catchExceptions(v_00_u03b5_5810_, v_00_u03b1_5811_, v_act_5812_, v_h_5813_);
    return v_res_5815_;
}
pub unsafe fn l_instMonadEIO___aux__1___redArg(
    mut v_f_5816_: *mut LeanObject,
    mut v_x_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5823_: u8 = 0;
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5828_: u8 = 0;
    let mut v_a_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5832_: u8 = 0;
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5819_ = lean_apply_1(v_x_5817_, lean_box(0));
                if lean_obj_tag(v___x_5819_) == 0 {
                    v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
                    v_isSharedCheck_5828_ = (!lean_is_exclusive(v___x_5819_)) as u8;
                    if v_isSharedCheck_5828_ == 0 {
                        v___x_5822_ = v___x_5819_;
                        v_isShared_5823_ = v_isSharedCheck_5828_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5820_);
                        lean_dec(v___x_5819_);
                        v___x_5822_ = lean_box(0);
                        v_isShared_5823_ = v_isSharedCheck_5828_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_5816_);
                    v_a_5829_ = lean_ctor_get(v___x_5819_, 0);
                    v_isSharedCheck_5836_ = (!lean_is_exclusive(v___x_5819_)) as u8;
                    if v_isSharedCheck_5836_ == 0 {
                        v___x_5831_ = v___x_5819_;
                        v_isShared_5832_ = v_isSharedCheck_5836_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5829_);
                        lean_dec(v___x_5819_);
                        v___x_5831_ = lean_box(0);
                        v_isShared_5832_ = v_isSharedCheck_5836_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5824_ = lean_apply_1(v_f_5816_, v_a_5820_);
                if v_isShared_5823_ == 0 {
                    lean_ctor_set(v___x_5822_, 0, v___x_5824_);
                    v___x_5826_ = v___x_5822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5827_, 0, v___x_5824_);
                    v___x_5826_ = v_reuseFailAlloc_5827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5826_;
            }
            3 => {
                if v_isShared_5832_ == 0 {
                    v___x_5834_ = v___x_5831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5829_);
                    v___x_5834_ = v_reuseFailAlloc_5835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__1___redArg___boxed(
    mut v_f_5837_: *mut LeanObject,
    mut v_x_5838_: *mut LeanObject,
    mut v_a_5839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5840_: *mut LeanObject = core::ptr::null_mut();
    v_res_5840_ = l_instMonadEIO___aux__1___redArg(v_f_5837_, v_x_5838_);
    return v_res_5840_;
}
pub unsafe fn l_instMonadEIO___aux__1(
    mut v_00_u03b5_5841_: *mut LeanObject,
    mut v_00_u03b1_5842_: *mut LeanObject,
    mut v_00_u03b2_5843_: *mut LeanObject,
    mut v_f_5844_: *mut LeanObject,
    mut v_x_5845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_a_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5860_: u8 = 0;
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5847_ = lean_apply_1(v_x_5845_, lean_box(0));
                if lean_obj_tag(v___x_5847_) == 0 {
                    v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
                    v_isSharedCheck_5856_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5856_ == 0 {
                        v___x_5850_ = v___x_5847_;
                        v_isShared_5851_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5848_);
                        lean_dec(v___x_5847_);
                        v___x_5850_ = lean_box(0);
                        v_isShared_5851_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_5844_);
                    v_a_5857_ = lean_ctor_get(v___x_5847_, 0);
                    v_isSharedCheck_5864_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5864_ == 0 {
                        v___x_5859_ = v___x_5847_;
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5857_);
                        lean_dec(v___x_5847_);
                        v___x_5859_ = lean_box(0);
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5852_ = lean_apply_1(v_f_5844_, v_a_5848_);
                if v_isShared_5851_ == 0 {
                    lean_ctor_set(v___x_5850_, 0, v___x_5852_);
                    v___x_5854_ = v___x_5850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
                    v___x_5854_ = v_reuseFailAlloc_5855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5854_;
            }
            3 => {
                if v_isShared_5860_ == 0 {
                    v___x_5862_ = v___x_5859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__1___boxed(
    mut v_00_u03b5_5865_: *mut LeanObject,
    mut v_00_u03b1_5866_: *mut LeanObject,
    mut v_00_u03b2_5867_: *mut LeanObject,
    mut v_f_5868_: *mut LeanObject,
    mut v_x_5869_: *mut LeanObject,
    mut v_a_5870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5871_: *mut LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_instMonadEIO___aux__1(
        v_00_u03b5_5865_,
        v_00_u03b1_5866_,
        v_00_u03b2_5867_,
        v_f_5868_,
        v_x_5869_,
    );
    return v_res_5871_;
}
pub unsafe fn l_instMonadEIO___aux__3___redArg(
    mut v_a_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5878_: u8 = 0;
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_unused_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5875_ = lean_apply_1(v_a_5873_, lean_box(0));
                if lean_obj_tag(v___x_5875_) == 0 {
                    v_isSharedCheck_5882_ = (!lean_is_exclusive(v___x_5875_)) as u8;
                    if v_isSharedCheck_5882_ == 0 {
                        v_unused_5883_ = lean_ctor_get(v___x_5875_, 0);
                        lean_dec(v_unused_5883_);
                        v___x_5877_ = v___x_5875_;
                        v_isShared_5878_ = v_isSharedCheck_5882_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5875_);
                        v___x_5877_ = lean_box(0);
                        v_isShared_5878_ = v_isSharedCheck_5882_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5872_);
                    v_a_5884_ = lean_ctor_get(v___x_5875_, 0);
                    v_isSharedCheck_5891_ = (!lean_is_exclusive(v___x_5875_)) as u8;
                    if v_isSharedCheck_5891_ == 0 {
                        v___x_5886_ = v___x_5875_;
                        v_isShared_5887_ = v_isSharedCheck_5891_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5884_);
                        lean_dec(v___x_5875_);
                        v___x_5886_ = lean_box(0);
                        v_isShared_5887_ = v_isSharedCheck_5891_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5878_ == 0 {
                    lean_ctor_set(v___x_5877_, 0, v_a_5872_);
                    v___x_5880_ = v___x_5877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5872_);
                    v___x_5880_ = v_reuseFailAlloc_5881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5880_;
            }
            3 => {
                if v_isShared_5887_ == 0 {
                    v___x_5889_ = v___x_5886_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
                    v___x_5889_ = v_reuseFailAlloc_5890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__3___redArg___boxed(
    mut v_a_5892_: *mut LeanObject,
    mut v_a_5893_: *mut LeanObject,
    mut v_a_5894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5895_: *mut LeanObject = core::ptr::null_mut();
    v_res_5895_ = l_instMonadEIO___aux__3___redArg(v_a_5892_, v_a_5893_);
    return v_res_5895_;
}
pub unsafe fn l_instMonadEIO___aux__3(
    mut v_00_u03b5_5896_: *mut LeanObject,
    mut v_00_u03b1_5897_: *mut LeanObject,
    mut v_00_u03b2_5898_: *mut LeanObject,
    mut v_a_5899_: *mut LeanObject,
    mut v_a_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5909_: u8 = 0;
    let mut v_unused_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5914_: u8 = 0;
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5902_ = lean_apply_1(v_a_5900_, lean_box(0));
                if lean_obj_tag(v___x_5902_) == 0 {
                    v_isSharedCheck_5909_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5909_ == 0 {
                        v_unused_5910_ = lean_ctor_get(v___x_5902_, 0);
                        lean_dec(v_unused_5910_);
                        v___x_5904_ = v___x_5902_;
                        v_isShared_5905_ = v_isSharedCheck_5909_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5902_);
                        v___x_5904_ = lean_box(0);
                        v_isShared_5905_ = v_isSharedCheck_5909_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5899_);
                    v_a_5911_ = lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5918_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5918_ == 0 {
                        v___x_5913_ = v___x_5902_;
                        v_isShared_5914_ = v_isSharedCheck_5918_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5911_);
                        lean_dec(v___x_5902_);
                        v___x_5913_ = lean_box(0);
                        v_isShared_5914_ = v_isSharedCheck_5918_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5905_ == 0 {
                    lean_ctor_set(v___x_5904_, 0, v_a_5899_);
                    v___x_5907_ = v___x_5904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_a_5899_);
                    v___x_5907_ = v_reuseFailAlloc_5908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5907_;
            }
            3 => {
                if v_isShared_5914_ == 0 {
                    v___x_5916_ = v___x_5913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
                    v___x_5916_ = v_reuseFailAlloc_5917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__3___boxed(
    mut v_00_u03b5_5919_: *mut LeanObject,
    mut v_00_u03b1_5920_: *mut LeanObject,
    mut v_00_u03b2_5921_: *mut LeanObject,
    mut v_a_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5925_: *mut LeanObject = core::ptr::null_mut();
    v_res_5925_ = l_instMonadEIO___aux__3(
        v_00_u03b5_5919_,
        v_00_u03b1_5920_,
        v_00_u03b2_5921_,
        v_a_5922_,
        v_a_5923_,
    );
    return v_res_5925_;
}
pub unsafe fn l_instMonadEIO___aux__5___redArg(mut v_a_5926_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    v___x_5928_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5928_, 0, v_a_5926_);
    return v___x_5928_;
}
pub unsafe fn l_instMonadEIO___aux__5___redArg___boxed(
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5931_: *mut LeanObject = core::ptr::null_mut();
    v_res_5931_ = l_instMonadEIO___aux__5___redArg(v_a_5929_);
    return v_res_5931_;
}
pub unsafe fn l_instMonadEIO___aux__5(
    mut v_00_u03b5_5932_: *mut LeanObject,
    mut v_00_u03b1_5933_: *mut LeanObject,
    mut v_a_5934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    v___x_5936_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5936_, 0, v_a_5934_);
    return v___x_5936_;
}
pub unsafe fn l_instMonadEIO___aux__5___boxed(
    mut v_00_u03b5_5937_: *mut LeanObject,
    mut v_00_u03b1_5938_: *mut LeanObject,
    mut v_a_5939_: *mut LeanObject,
    mut v_a_5940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5941_: *mut LeanObject = core::ptr::null_mut();
    v_res_5941_ = l_instMonadEIO___aux__5(v_00_u03b5_5937_, v_00_u03b1_5938_, v_a_5939_);
    return v_res_5941_;
}
pub unsafe fn l_instMonadEIO___aux__7___redArg(
    mut v_f_5942_: *mut LeanObject,
    mut v_x_5943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5952_: u8 = 0;
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5957_: u8 = 0;
    let mut v_a_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5961_: u8 = 0;
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5965_: u8 = 0;
    let mut v_a_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5945_ = lean_apply_1(v_f_5942_, lean_box(0));
                if lean_obj_tag(v___x_5945_) == 0 {
                    v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
                    lean_inc(v_a_5946_);
                    lean_dec_ref_known(v___x_5945_, 1);
                    v___x_5947_ = lean_box(0);
                    v___x_5948_ = lean_apply_2(v_x_5943_, v___x_5947_, lean_box(0));
                    if lean_obj_tag(v___x_5948_) == 0 {
                        v_a_5949_ = lean_ctor_get(v___x_5948_, 0);
                        v_isSharedCheck_5957_ = (!lean_is_exclusive(v___x_5948_)) as u8;
                        if v_isSharedCheck_5957_ == 0 {
                            v___x_5951_ = v___x_5948_;
                            v_isShared_5952_ = v_isSharedCheck_5957_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5949_);
                            lean_dec(v___x_5948_);
                            v___x_5951_ = lean_box(0);
                            v_isShared_5952_ = v_isSharedCheck_5957_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5946_);
                        v_a_5958_ = lean_ctor_get(v___x_5948_, 0);
                        v_isSharedCheck_5965_ = (!lean_is_exclusive(v___x_5948_)) as u8;
                        if v_isSharedCheck_5965_ == 0 {
                            v___x_5960_ = v___x_5948_;
                            v_isShared_5961_ = v_isSharedCheck_5965_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5958_);
                            lean_dec(v___x_5948_);
                            v___x_5960_ = lean_box(0);
                            v_isShared_5961_ = v_isSharedCheck_5965_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_5943_);
                    v_a_5966_ = lean_ctor_get(v___x_5945_, 0);
                    v_isSharedCheck_5973_ = (!lean_is_exclusive(v___x_5945_)) as u8;
                    if v_isSharedCheck_5973_ == 0 {
                        v___x_5968_ = v___x_5945_;
                        v_isShared_5969_ = v_isSharedCheck_5973_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5966_);
                        lean_dec(v___x_5945_);
                        v___x_5968_ = lean_box(0);
                        v_isShared_5969_ = v_isSharedCheck_5973_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5953_ = lean_apply_1(v_a_5946_, v_a_5949_);
                if v_isShared_5952_ == 0 {
                    lean_ctor_set(v___x_5951_, 0, v___x_5953_);
                    v___x_5955_ = v___x_5951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___x_5953_);
                    v___x_5955_ = v_reuseFailAlloc_5956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5955_;
            }
            3 => {
                if v_isShared_5961_ == 0 {
                    v___x_5963_ = v___x_5960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
                    v___x_5963_ = v_reuseFailAlloc_5964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5963_;
            }
            5 => {
                if v_isShared_5969_ == 0 {
                    v___x_5971_ = v___x_5968_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
                    v___x_5971_ = v_reuseFailAlloc_5972_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__7___redArg___boxed(
    mut v_f_5974_: *mut LeanObject,
    mut v_x_5975_: *mut LeanObject,
    mut v_a_5976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5977_: *mut LeanObject = core::ptr::null_mut();
    v_res_5977_ = l_instMonadEIO___aux__7___redArg(v_f_5974_, v_x_5975_);
    return v_res_5977_;
}
pub unsafe fn l_instMonadEIO___aux__7(
    mut v_00_u03b5_5978_: *mut LeanObject,
    mut v_00_u03b1_5979_: *mut LeanObject,
    mut v_00_u03b2_5980_: *mut LeanObject,
    mut v_f_5981_: *mut LeanObject,
    mut v_x_5982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5991_: u8 = 0;
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5996_: u8 = 0;
    let mut v_a_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6000_: u8 = 0;
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6004_: u8 = 0;
    let mut v_a_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6008_: u8 = 0;
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5984_ = lean_apply_1(v_f_5981_, lean_box(0));
                if lean_obj_tag(v___x_5984_) == 0 {
                    v_a_5985_ = lean_ctor_get(v___x_5984_, 0);
                    lean_inc(v_a_5985_);
                    lean_dec_ref_known(v___x_5984_, 1);
                    v___x_5986_ = lean_box(0);
                    v___x_5987_ = lean_apply_2(v_x_5982_, v___x_5986_, lean_box(0));
                    if lean_obj_tag(v___x_5987_) == 0 {
                        v_a_5988_ = lean_ctor_get(v___x_5987_, 0);
                        v_isSharedCheck_5996_ = (!lean_is_exclusive(v___x_5987_)) as u8;
                        if v_isSharedCheck_5996_ == 0 {
                            v___x_5990_ = v___x_5987_;
                            v_isShared_5991_ = v_isSharedCheck_5996_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5988_);
                            lean_dec(v___x_5987_);
                            v___x_5990_ = lean_box(0);
                            v_isShared_5991_ = v_isSharedCheck_5996_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5985_);
                        v_a_5997_ = lean_ctor_get(v___x_5987_, 0);
                        v_isSharedCheck_6004_ = (!lean_is_exclusive(v___x_5987_)) as u8;
                        if v_isSharedCheck_6004_ == 0 {
                            v___x_5999_ = v___x_5987_;
                            v_isShared_6000_ = v_isSharedCheck_6004_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5997_);
                            lean_dec(v___x_5987_);
                            v___x_5999_ = lean_box(0);
                            v_isShared_6000_ = v_isSharedCheck_6004_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_5982_);
                    v_a_6005_ = lean_ctor_get(v___x_5984_, 0);
                    v_isSharedCheck_6012_ = (!lean_is_exclusive(v___x_5984_)) as u8;
                    if v_isSharedCheck_6012_ == 0 {
                        v___x_6007_ = v___x_5984_;
                        v_isShared_6008_ = v_isSharedCheck_6012_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6005_);
                        lean_dec(v___x_5984_);
                        v___x_6007_ = lean_box(0);
                        v_isShared_6008_ = v_isSharedCheck_6012_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5992_ = lean_apply_1(v_a_5985_, v_a_5988_);
                if v_isShared_5991_ == 0 {
                    lean_ctor_set(v___x_5990_, 0, v___x_5992_);
                    v___x_5994_ = v___x_5990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5992_);
                    v___x_5994_ = v_reuseFailAlloc_5995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5994_;
            }
            3 => {
                if v_isShared_6000_ == 0 {
                    v___x_6002_ = v___x_5999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_a_5997_);
                    v___x_6002_ = v_reuseFailAlloc_6003_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6002_;
            }
            5 => {
                if v_isShared_6008_ == 0 {
                    v___x_6010_ = v___x_6007_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
                    v___x_6010_ = v_reuseFailAlloc_6011_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__7___boxed(
    mut v_00_u03b5_6013_: *mut LeanObject,
    mut v_00_u03b1_6014_: *mut LeanObject,
    mut v_00_u03b2_6015_: *mut LeanObject,
    mut v_f_6016_: *mut LeanObject,
    mut v_x_6017_: *mut LeanObject,
    mut v_a_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6019_: *mut LeanObject = core::ptr::null_mut();
    v_res_6019_ = l_instMonadEIO___aux__7(
        v_00_u03b5_6013_,
        v_00_u03b1_6014_,
        v_00_u03b2_6015_,
        v_f_6016_,
        v_x_6017_,
    );
    return v_res_6019_;
}
pub unsafe fn l_instMonadEIO___aux__9___redArg(
    mut v_x_6020_: *mut LeanObject,
    mut v_y_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6029_: u8 = 0;
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6033_: u8 = 0;
    let mut v_unused_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6038_: u8 = 0;
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6023_ = lean_apply_1(v_x_6020_, lean_box(0));
                if lean_obj_tag(v___x_6023_) == 0 {
                    v_a_6024_ = lean_ctor_get(v___x_6023_, 0);
                    lean_inc(v_a_6024_);
                    lean_dec_ref_known(v___x_6023_, 1);
                    v___x_6025_ = lean_box(0);
                    v___x_6026_ = lean_apply_2(v_y_6021_, v___x_6025_, lean_box(0));
                    if lean_obj_tag(v___x_6026_) == 0 {
                        v_isSharedCheck_6033_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6033_ == 0 {
                            v_unused_6034_ = lean_ctor_get(v___x_6026_, 0);
                            lean_dec(v_unused_6034_);
                            v___x_6028_ = v___x_6026_;
                            v_isShared_6029_ = v_isSharedCheck_6033_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6026_);
                            v___x_6028_ = lean_box(0);
                            v_isShared_6029_ = v_isSharedCheck_6033_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6024_);
                        v_a_6035_ = lean_ctor_get(v___x_6026_, 0);
                        v_isSharedCheck_6042_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                        if v_isSharedCheck_6042_ == 0 {
                            v___x_6037_ = v___x_6026_;
                            v_isShared_6038_ = v_isSharedCheck_6042_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6035_);
                            lean_dec(v___x_6026_);
                            v___x_6037_ = lean_box(0);
                            v_isShared_6038_ = v_isSharedCheck_6042_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_y_6021_);
                    return v___x_6023_;
                }
            }
            1 => {
                if v_isShared_6029_ == 0 {
                    lean_ctor_set(v___x_6028_, 0, v_a_6024_);
                    v___x_6031_ = v___x_6028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6032_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6032_, 0, v_a_6024_);
                    v___x_6031_ = v_reuseFailAlloc_6032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6031_;
            }
            3 => {
                if v_isShared_6038_ == 0 {
                    v___x_6040_ = v___x_6037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6041_, 0, v_a_6035_);
                    v___x_6040_ = v_reuseFailAlloc_6041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__9___redArg___boxed(
    mut v_x_6043_: *mut LeanObject,
    mut v_y_6044_: *mut LeanObject,
    mut v_a_6045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6046_: *mut LeanObject = core::ptr::null_mut();
    v_res_6046_ = l_instMonadEIO___aux__9___redArg(v_x_6043_, v_y_6044_);
    return v_res_6046_;
}
pub unsafe fn l_instMonadEIO___aux__9(
    mut v_00_u03b5_6047_: *mut LeanObject,
    mut v_00_u03b1_6048_: *mut LeanObject,
    mut v_00_u03b2_6049_: *mut LeanObject,
    mut v_x_6050_: *mut LeanObject,
    mut v_y_6051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_unused_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6068_: u8 = 0;
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6053_ = lean_apply_1(v_x_6050_, lean_box(0));
                if lean_obj_tag(v___x_6053_) == 0 {
                    v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
                    lean_inc(v_a_6054_);
                    lean_dec_ref_known(v___x_6053_, 1);
                    v___x_6055_ = lean_box(0);
                    v___x_6056_ = lean_apply_2(v_y_6051_, v___x_6055_, lean_box(0));
                    if lean_obj_tag(v___x_6056_) == 0 {
                        v_isSharedCheck_6063_ = (!lean_is_exclusive(v___x_6056_)) as u8;
                        if v_isSharedCheck_6063_ == 0 {
                            v_unused_6064_ = lean_ctor_get(v___x_6056_, 0);
                            lean_dec(v_unused_6064_);
                            v___x_6058_ = v___x_6056_;
                            v_isShared_6059_ = v_isSharedCheck_6063_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6056_);
                            v___x_6058_ = lean_box(0);
                            v_isShared_6059_ = v_isSharedCheck_6063_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6054_);
                        v_a_6065_ = lean_ctor_get(v___x_6056_, 0);
                        v_isSharedCheck_6072_ = (!lean_is_exclusive(v___x_6056_)) as u8;
                        if v_isSharedCheck_6072_ == 0 {
                            v___x_6067_ = v___x_6056_;
                            v_isShared_6068_ = v_isSharedCheck_6072_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6065_);
                            lean_dec(v___x_6056_);
                            v___x_6067_ = lean_box(0);
                            v_isShared_6068_ = v_isSharedCheck_6072_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_y_6051_);
                    return v___x_6053_;
                }
            }
            1 => {
                if v_isShared_6059_ == 0 {
                    lean_ctor_set(v___x_6058_, 0, v_a_6054_);
                    v___x_6061_ = v___x_6058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6054_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6061_;
            }
            3 => {
                if v_isShared_6068_ == 0 {
                    v___x_6070_ = v___x_6067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6071_, 0, v_a_6065_);
                    v___x_6070_ = v_reuseFailAlloc_6071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__9___boxed(
    mut v_00_u03b5_6073_: *mut LeanObject,
    mut v_00_u03b1_6074_: *mut LeanObject,
    mut v_00_u03b2_6075_: *mut LeanObject,
    mut v_x_6076_: *mut LeanObject,
    mut v_y_6077_: *mut LeanObject,
    mut v_a_6078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6079_: *mut LeanObject = core::ptr::null_mut();
    v_res_6079_ = l_instMonadEIO___aux__9(
        v_00_u03b5_6073_,
        v_00_u03b1_6074_,
        v_00_u03b2_6075_,
        v_x_6076_,
        v_y_6077_,
    );
    return v_res_6079_;
}
pub unsafe fn l_instMonadEIO___aux__11___redArg(
    mut v_x_6080_: *mut LeanObject,
    mut v_y_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6089_: u8 = 0;
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6083_ = lean_apply_1(v_x_6080_, lean_box(0));
                if lean_obj_tag(v___x_6083_) == 0 {
                    lean_dec_ref_known(v___x_6083_, 1);
                    v___x_6084_ = lean_box(0);
                    v___x_6085_ = lean_apply_2(v_y_6081_, v___x_6084_, lean_box(0));
                    return v___x_6085_;
                } else {
                    lean_dec_ref(v_y_6081_);
                    v_a_6086_ = lean_ctor_get(v___x_6083_, 0);
                    v_isSharedCheck_6093_ = (!lean_is_exclusive(v___x_6083_)) as u8;
                    if v_isSharedCheck_6093_ == 0 {
                        v___x_6088_ = v___x_6083_;
                        v_isShared_6089_ = v_isSharedCheck_6093_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6086_);
                        lean_dec(v___x_6083_);
                        v___x_6088_ = lean_box(0);
                        v_isShared_6089_ = v_isSharedCheck_6093_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6089_ == 0 {
                    v___x_6091_ = v___x_6088_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6092_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6092_, 0, v_a_6086_);
                    v___x_6091_ = v_reuseFailAlloc_6092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__11___redArg___boxed(
    mut v_x_6094_: *mut LeanObject,
    mut v_y_6095_: *mut LeanObject,
    mut v_a_6096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6097_: *mut LeanObject = core::ptr::null_mut();
    v_res_6097_ = l_instMonadEIO___aux__11___redArg(v_x_6094_, v_y_6095_);
    return v_res_6097_;
}
pub unsafe fn l_instMonadEIO___aux__11(
    mut v_00_u03b5_6098_: *mut LeanObject,
    mut v_00_u03b1_6099_: *mut LeanObject,
    mut v_00_u03b2_6100_: *mut LeanObject,
    mut v_x_6101_: *mut LeanObject,
    mut v_y_6102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6110_: u8 = 0;
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6104_ = lean_apply_1(v_x_6101_, lean_box(0));
                if lean_obj_tag(v___x_6104_) == 0 {
                    lean_dec_ref_known(v___x_6104_, 1);
                    v___x_6105_ = lean_box(0);
                    v___x_6106_ = lean_apply_2(v_y_6102_, v___x_6105_, lean_box(0));
                    return v___x_6106_;
                } else {
                    lean_dec_ref(v_y_6102_);
                    v_a_6107_ = lean_ctor_get(v___x_6104_, 0);
                    v_isSharedCheck_6114_ = (!lean_is_exclusive(v___x_6104_)) as u8;
                    if v_isSharedCheck_6114_ == 0 {
                        v___x_6109_ = v___x_6104_;
                        v_isShared_6110_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6107_);
                        lean_dec(v___x_6104_);
                        v___x_6109_ = lean_box(0);
                        v_isShared_6110_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6110_ == 0 {
                    v___x_6112_ = v___x_6109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_a_6107_);
                    v___x_6112_ = v_reuseFailAlloc_6113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__11___boxed(
    mut v_00_u03b5_6115_: *mut LeanObject,
    mut v_00_u03b1_6116_: *mut LeanObject,
    mut v_00_u03b2_6117_: *mut LeanObject,
    mut v_x_6118_: *mut LeanObject,
    mut v_y_6119_: *mut LeanObject,
    mut v_a_6120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6121_: *mut LeanObject = core::ptr::null_mut();
    v_res_6121_ = l_instMonadEIO___aux__11(
        v_00_u03b5_6115_,
        v_00_u03b1_6116_,
        v_00_u03b2_6117_,
        v_x_6118_,
        v_y_6119_,
    );
    return v_res_6121_;
}
pub unsafe fn l_instMonadEIO___aux__13___redArg(
    mut v_x_6122_: *mut LeanObject,
    mut v_f_6123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6125_ = lean_apply_1(v_x_6122_, lean_box(0));
                if lean_obj_tag(v___x_6125_) == 0 {
                    v_a_6126_ = lean_ctor_get(v___x_6125_, 0);
                    lean_inc(v_a_6126_);
                    lean_dec_ref_known(v___x_6125_, 1);
                    v___x_6127_ = lean_apply_2(v_f_6123_, v_a_6126_, lean_box(0));
                    return v___x_6127_;
                } else {
                    lean_dec_ref(v_f_6123_);
                    v_a_6128_ = lean_ctor_get(v___x_6125_, 0);
                    v_isSharedCheck_6135_ = (!lean_is_exclusive(v___x_6125_)) as u8;
                    if v_isSharedCheck_6135_ == 0 {
                        v___x_6130_ = v___x_6125_;
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6128_);
                        lean_dec(v___x_6125_);
                        v___x_6130_ = lean_box(0);
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6131_ == 0 {
                    v___x_6133_ = v___x_6130_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6128_);
                    v___x_6133_ = v_reuseFailAlloc_6134_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__13___redArg___boxed(
    mut v_x_6136_: *mut LeanObject,
    mut v_f_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6139_: *mut LeanObject = core::ptr::null_mut();
    v_res_6139_ = l_instMonadEIO___aux__13___redArg(v_x_6136_, v_f_6137_);
    return v_res_6139_;
}
pub unsafe fn l_instMonadEIO___aux__13(
    mut v_00_u03b5_6140_: *mut LeanObject,
    mut v_00_u03b1_6141_: *mut LeanObject,
    mut v_00_u03b2_6142_: *mut LeanObject,
    mut v_x_6143_: *mut LeanObject,
    mut v_f_6144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6152_: u8 = 0;
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6146_ = lean_apply_1(v_x_6143_, lean_box(0));
                if lean_obj_tag(v___x_6146_) == 0 {
                    v_a_6147_ = lean_ctor_get(v___x_6146_, 0);
                    lean_inc(v_a_6147_);
                    lean_dec_ref_known(v___x_6146_, 1);
                    v___x_6148_ = lean_apply_2(v_f_6144_, v_a_6147_, lean_box(0));
                    return v___x_6148_;
                } else {
                    lean_dec_ref(v_f_6144_);
                    v_a_6149_ = lean_ctor_get(v___x_6146_, 0);
                    v_isSharedCheck_6156_ = (!lean_is_exclusive(v___x_6146_)) as u8;
                    if v_isSharedCheck_6156_ == 0 {
                        v___x_6151_ = v___x_6146_;
                        v_isShared_6152_ = v_isSharedCheck_6156_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6149_);
                        lean_dec(v___x_6146_);
                        v___x_6151_ = lean_box(0);
                        v_isShared_6152_ = v_isSharedCheck_6156_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6152_ == 0 {
                    v___x_6154_ = v___x_6151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6155_, 0, v_a_6149_);
                    v___x_6154_ = v_reuseFailAlloc_6155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadEIO___aux__13___boxed(
    mut v_00_u03b5_6157_: *mut LeanObject,
    mut v_00_u03b1_6158_: *mut LeanObject,
    mut v_00_u03b2_6159_: *mut LeanObject,
    mut v_x_6160_: *mut LeanObject,
    mut v_f_6161_: *mut LeanObject,
    mut v_a_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6163_: *mut LeanObject = core::ptr::null_mut();
    v_res_6163_ = l_instMonadEIO___aux__13(
        v_00_u03b5_6157_,
        v_00_u03b1_6158_,
        v_00_u03b2_6159_,
        v_x_6160_,
        v_f_6161_,
    );
    return v_res_6163_;
}
pub unsafe fn l_instMonadEIO(mut v_00_u03b5_6183_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    v___x_6184_ = l_instMonadEIO___closed__9;
    return v___x_6184_;
}
pub unsafe fn l_instMonadFinallyEIO___aux__1___redArg(
    mut v_x_6185_: *mut LeanObject,
    mut v_f_6186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6192_: u8 = 0;
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6199_: u8 = 0;
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6204_: u8 = 0;
    let mut v_a_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6208_: u8 = 0;
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6212_: u8 = 0;
    let mut v_reuseFailAlloc_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6214_: u8 = 0;
    let mut v_a_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6220_: u8 = 0;
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6224_: u8 = 0;
    let mut v_unused_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6229_: u8 = 0;
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_6188_ = lean_apply_1(v_x_6185_, lean_box(0));
                if lean_obj_tag(v_r_6188_) == 0 {
                    v_a_6189_ = lean_ctor_get(v_r_6188_, 0);
                    v_isSharedCheck_6214_ = (!lean_is_exclusive(v_r_6188_)) as u8;
                    if v_isSharedCheck_6214_ == 0 {
                        v___x_6191_ = v_r_6188_;
                        v_isShared_6192_ = v_isSharedCheck_6214_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6189_);
                        lean_dec(v_r_6188_);
                        v___x_6191_ = lean_box(0);
                        v_isShared_6192_ = v_isSharedCheck_6214_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6215_ = lean_ctor_get(v_r_6188_, 0);
                    lean_inc(v_a_6215_);
                    lean_dec_ref_known(v_r_6188_, 1);
                    v___x_6216_ = lean_box(0);
                    v___x_6217_ = lean_apply_2(v_f_6186_, v___x_6216_, lean_box(0));
                    if lean_obj_tag(v___x_6217_) == 0 {
                        v_isSharedCheck_6224_ = (!lean_is_exclusive(v___x_6217_)) as u8;
                        if v_isSharedCheck_6224_ == 0 {
                            v_unused_6225_ = lean_ctor_get(v___x_6217_, 0);
                            lean_dec(v_unused_6225_);
                            v___x_6219_ = v___x_6217_;
                            v_isShared_6220_ = v_isSharedCheck_6224_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_6217_);
                            v___x_6219_ = lean_box(0);
                            v_isShared_6220_ = v_isSharedCheck_6224_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6215_);
                        v_a_6226_ = lean_ctor_get(v___x_6217_, 0);
                        v_isSharedCheck_6233_ = (!lean_is_exclusive(v___x_6217_)) as u8;
                        if v_isSharedCheck_6233_ == 0 {
                            v___x_6228_ = v___x_6217_;
                            v_isShared_6229_ = v_isSharedCheck_6233_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6226_);
                            lean_dec(v___x_6217_);
                            v___x_6228_ = lean_box(0);
                            v_isShared_6229_ = v_isSharedCheck_6233_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_6189_);
                if v_isShared_6192_ == 0 {
                    lean_ctor_set_tag(v___x_6191_, 1);
                    v___x_6194_ = v___x_6191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6213_, 0, v_a_6189_);
                    v___x_6194_ = v_reuseFailAlloc_6213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6195_ = lean_apply_2(v_f_6186_, v___x_6194_, lean_box(0));
                if lean_obj_tag(v___x_6195_) == 0 {
                    v_a_6196_ = lean_ctor_get(v___x_6195_, 0);
                    v_isSharedCheck_6204_ = (!lean_is_exclusive(v___x_6195_)) as u8;
                    if v_isSharedCheck_6204_ == 0 {
                        v___x_6198_ = v___x_6195_;
                        v_isShared_6199_ = v_isSharedCheck_6204_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6196_);
                        lean_dec(v___x_6195_);
                        v___x_6198_ = lean_box(0);
                        v_isShared_6199_ = v_isSharedCheck_6204_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6189_);
                    v_a_6205_ = lean_ctor_get(v___x_6195_, 0);
                    v_isSharedCheck_6212_ = (!lean_is_exclusive(v___x_6195_)) as u8;
                    if v_isSharedCheck_6212_ == 0 {
                        v___x_6207_ = v___x_6195_;
                        v_isShared_6208_ = v_isSharedCheck_6212_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6205_);
                        lean_dec(v___x_6195_);
                        v___x_6207_ = lean_box(0);
                        v_isShared_6208_ = v_isSharedCheck_6212_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6200_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6200_, 0, v_a_6189_);
                lean_ctor_set(v___x_6200_, 1, v_a_6196_);
                if v_isShared_6199_ == 0 {
                    lean_ctor_set(v___x_6198_, 0, v___x_6200_);
                    v___x_6202_ = v___x_6198_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6203_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 0, v___x_6200_);
                    v___x_6202_ = v_reuseFailAlloc_6203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6202_;
            }
            5 => {
                if v_isShared_6208_ == 0 {
                    v___x_6210_ = v___x_6207_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6211_, 0, v_a_6205_);
                    v___x_6210_ = v_reuseFailAlloc_6211_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6210_;
            }
            7 => {
                if v_isShared_6220_ == 0 {
                    lean_ctor_set_tag(v___x_6219_, 1);
                    lean_ctor_set(v___x_6219_, 0, v_a_6215_);
                    v___x_6222_ = v___x_6219_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6223_, 0, v_a_6215_);
                    v___x_6222_ = v_reuseFailAlloc_6223_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6222_;
            }
            9 => {
                if v_isShared_6229_ == 0 {
                    v___x_6231_ = v___x_6228_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadFinallyEIO___aux__1___redArg___boxed(
    mut v_x_6234_: *mut LeanObject,
    mut v_f_6235_: *mut LeanObject,
    mut v_s_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6237_: *mut LeanObject = core::ptr::null_mut();
    v_res_6237_ = l_instMonadFinallyEIO___aux__1___redArg(v_x_6234_, v_f_6235_);
    return v_res_6237_;
}
pub unsafe fn l_instMonadFinallyEIO___aux__1(
    mut v_00_u03b5_6238_: *mut LeanObject,
    mut v_00_u03b1_6239_: *mut LeanObject,
    mut v_00_u03b2_6240_: *mut LeanObject,
    mut v_x_6241_: *mut LeanObject,
    mut v_f_6242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6248_: u8 = 0;
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6260_: u8 = 0;
    let mut v_a_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6264_: u8 = 0;
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6268_: u8 = 0;
    let mut v_reuseFailAlloc_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_a_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6276_: u8 = 0;
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6280_: u8 = 0;
    let mut v_unused_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6285_: u8 = 0;
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_6244_ = lean_apply_1(v_x_6241_, lean_box(0));
                if lean_obj_tag(v_r_6244_) == 0 {
                    v_a_6245_ = lean_ctor_get(v_r_6244_, 0);
                    v_isSharedCheck_6270_ = (!lean_is_exclusive(v_r_6244_)) as u8;
                    if v_isSharedCheck_6270_ == 0 {
                        v___x_6247_ = v_r_6244_;
                        v_isShared_6248_ = v_isSharedCheck_6270_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6245_);
                        lean_dec(v_r_6244_);
                        v___x_6247_ = lean_box(0);
                        v_isShared_6248_ = v_isSharedCheck_6270_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6271_ = lean_ctor_get(v_r_6244_, 0);
                    lean_inc(v_a_6271_);
                    lean_dec_ref_known(v_r_6244_, 1);
                    v___x_6272_ = lean_box(0);
                    v___x_6273_ = lean_apply_2(v_f_6242_, v___x_6272_, lean_box(0));
                    if lean_obj_tag(v___x_6273_) == 0 {
                        v_isSharedCheck_6280_ = (!lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6280_ == 0 {
                            v_unused_6281_ = lean_ctor_get(v___x_6273_, 0);
                            lean_dec(v_unused_6281_);
                            v___x_6275_ = v___x_6273_;
                            v_isShared_6276_ = v_isSharedCheck_6280_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_6273_);
                            v___x_6275_ = lean_box(0);
                            v_isShared_6276_ = v_isSharedCheck_6280_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6271_);
                        v_a_6282_ = lean_ctor_get(v___x_6273_, 0);
                        v_isSharedCheck_6289_ = (!lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6289_ == 0 {
                            v___x_6284_ = v___x_6273_;
                            v_isShared_6285_ = v_isSharedCheck_6289_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6282_);
                            lean_dec(v___x_6273_);
                            v___x_6284_ = lean_box(0);
                            v_isShared_6285_ = v_isSharedCheck_6289_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_6245_);
                if v_isShared_6248_ == 0 {
                    lean_ctor_set_tag(v___x_6247_, 1);
                    v___x_6250_ = v___x_6247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6245_);
                    v___x_6250_ = v_reuseFailAlloc_6269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6251_ = lean_apply_2(v_f_6242_, v___x_6250_, lean_box(0));
                if lean_obj_tag(v___x_6251_) == 0 {
                    v_a_6252_ = lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6260_ = (!lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6260_ == 0 {
                        v___x_6254_ = v___x_6251_;
                        v_isShared_6255_ = v_isSharedCheck_6260_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6252_);
                        lean_dec(v___x_6251_);
                        v___x_6254_ = lean_box(0);
                        v_isShared_6255_ = v_isSharedCheck_6260_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6245_);
                    v_a_6261_ = lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6268_ = (!lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6268_ == 0 {
                        v___x_6263_ = v___x_6251_;
                        v_isShared_6264_ = v_isSharedCheck_6268_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6261_);
                        lean_dec(v___x_6251_);
                        v___x_6263_ = lean_box(0);
                        v_isShared_6264_ = v_isSharedCheck_6268_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6256_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6256_, 0, v_a_6245_);
                lean_ctor_set(v___x_6256_, 1, v_a_6252_);
                if v_isShared_6255_ == 0 {
                    lean_ctor_set(v___x_6254_, 0, v___x_6256_);
                    v___x_6258_ = v___x_6254_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6259_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6259_, 0, v___x_6256_);
                    v___x_6258_ = v_reuseFailAlloc_6259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6258_;
            }
            5 => {
                if v_isShared_6264_ == 0 {
                    v___x_6266_ = v___x_6263_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6267_, 0, v_a_6261_);
                    v___x_6266_ = v_reuseFailAlloc_6267_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6266_;
            }
            7 => {
                if v_isShared_6276_ == 0 {
                    lean_ctor_set_tag(v___x_6275_, 1);
                    lean_ctor_set(v___x_6275_, 0, v_a_6271_);
                    v___x_6278_ = v___x_6275_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_a_6271_);
                    v___x_6278_ = v_reuseFailAlloc_6279_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6278_;
            }
            9 => {
                if v_isShared_6285_ == 0 {
                    v___x_6287_ = v___x_6284_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_a_6282_);
                    v___x_6287_ = v_reuseFailAlloc_6288_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadFinallyEIO___aux__1___boxed(
    mut v_00_u03b5_6290_: *mut LeanObject,
    mut v_00_u03b1_6291_: *mut LeanObject,
    mut v_00_u03b2_6292_: *mut LeanObject,
    mut v_x_6293_: *mut LeanObject,
    mut v_f_6294_: *mut LeanObject,
    mut v_s_6295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6296_: *mut LeanObject = core::ptr::null_mut();
    v_res_6296_ = l_instMonadFinallyEIO___aux__1(
        v_00_u03b5_6290_,
        v_00_u03b1_6291_,
        v_00_u03b2_6292_,
        v_x_6293_,
        v_f_6294_,
    );
    return v_res_6296_;
}
pub unsafe fn l_instMonadFinallyEIO(mut v_00_u03b5_6298_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    v___x_6299_ = l_instMonadFinallyEIO___closed__0;
    return v___x_6299_;
}
pub unsafe fn l_instMonadAttachEIO___aux__3___redArg(
    mut v_x_6300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_a_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6302_ = lean_apply_1(v_x_6300_, lean_box(0));
                if lean_obj_tag(v___x_6302_) == 0 {
                    v_a_6303_ = lean_ctor_get(v___x_6302_, 0);
                    v_isSharedCheck_6310_ = (!lean_is_exclusive(v___x_6302_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6305_ = v___x_6302_;
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6303_);
                        lean_dec(v___x_6302_);
                        v___x_6305_ = lean_box(0);
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6311_ = lean_ctor_get(v___x_6302_, 0);
                    v_isSharedCheck_6318_ = (!lean_is_exclusive(v___x_6302_)) as u8;
                    if v_isSharedCheck_6318_ == 0 {
                        v___x_6313_ = v___x_6302_;
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6311_);
                        lean_dec(v___x_6302_);
                        v___x_6313_ = lean_box(0);
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6306_ == 0 {
                    v___x_6308_ = v___x_6305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6309_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
                    v___x_6308_ = v_reuseFailAlloc_6309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6308_;
            }
            3 => {
                if v_isShared_6314_ == 0 {
                    v___x_6316_ = v___x_6313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
                    v___x_6316_ = v_reuseFailAlloc_6317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadAttachEIO___aux__3___redArg___boxed(
    mut v_x_6319_: *mut LeanObject,
    mut v_s_6320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6321_: *mut LeanObject = core::ptr::null_mut();
    v_res_6321_ = l_instMonadAttachEIO___aux__3___redArg(v_x_6319_);
    return v_res_6321_;
}
pub unsafe fn l_instMonadAttachEIO___aux__3(
    mut v_00_u03b5_6322_: *mut LeanObject,
    mut v_00_u03b1_6323_: *mut LeanObject,
    mut v_x_6324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6330_: u8 = 0;
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6334_: u8 = 0;
    let mut v_a_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6338_: u8 = 0;
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6326_ = lean_apply_1(v_x_6324_, lean_box(0));
                if lean_obj_tag(v___x_6326_) == 0 {
                    v_a_6327_ = lean_ctor_get(v___x_6326_, 0);
                    v_isSharedCheck_6334_ = (!lean_is_exclusive(v___x_6326_)) as u8;
                    if v_isSharedCheck_6334_ == 0 {
                        v___x_6329_ = v___x_6326_;
                        v_isShared_6330_ = v_isSharedCheck_6334_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6327_);
                        lean_dec(v___x_6326_);
                        v___x_6329_ = lean_box(0);
                        v_isShared_6330_ = v_isSharedCheck_6334_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6335_ = lean_ctor_get(v___x_6326_, 0);
                    v_isSharedCheck_6342_ = (!lean_is_exclusive(v___x_6326_)) as u8;
                    if v_isSharedCheck_6342_ == 0 {
                        v___x_6337_ = v___x_6326_;
                        v_isShared_6338_ = v_isSharedCheck_6342_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6335_);
                        lean_dec(v___x_6326_);
                        v___x_6337_ = lean_box(0);
                        v_isShared_6338_ = v_isSharedCheck_6342_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6330_ == 0 {
                    v___x_6332_ = v___x_6329_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_a_6327_);
                    v___x_6332_ = v_reuseFailAlloc_6333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6332_;
            }
            3 => {
                if v_isShared_6338_ == 0 {
                    v___x_6340_ = v___x_6337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6341_, 0, v_a_6335_);
                    v___x_6340_ = v_reuseFailAlloc_6341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadAttachEIO___aux__3___boxed(
    mut v_00_u03b5_6343_: *mut LeanObject,
    mut v_00_u03b1_6344_: *mut LeanObject,
    mut v_x_6345_: *mut LeanObject,
    mut v_s_6346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6347_: *mut LeanObject = core::ptr::null_mut();
    v_res_6347_ = l_instMonadAttachEIO___aux__3(v_00_u03b5_6343_, v_00_u03b1_6344_, v_x_6345_);
    return v_res_6347_;
}
pub unsafe fn l_instMonadAttachEIO(mut v_00_u03b5_6349_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    v___x_6350_ = l_instMonadAttachEIO___closed__0;
    return v___x_6350_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__1___redArg(
    mut v_e_6351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    v___x_6353_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6353_, 0, v_e_6351_);
    return v___x_6353_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__1___redArg___boxed(
    mut v_e_6354_: *mut LeanObject,
    mut v_a_6355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6356_: *mut LeanObject = core::ptr::null_mut();
    v_res_6356_ = l_instMonadExceptOfEIO___aux__1___redArg(v_e_6354_);
    return v_res_6356_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__1(
    mut v_00_u03b5_6357_: *mut LeanObject,
    mut v_00_u03b1_6358_: *mut LeanObject,
    mut v_e_6359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    v___x_6361_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6361_, 0, v_e_6359_);
    return v___x_6361_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__1___boxed(
    mut v_00_u03b5_6362_: *mut LeanObject,
    mut v_00_u03b1_6363_: *mut LeanObject,
    mut v_e_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6366_: *mut LeanObject = core::ptr::null_mut();
    v_res_6366_ = l_instMonadExceptOfEIO___aux__1(v_00_u03b5_6362_, v_00_u03b1_6363_, v_e_6364_);
    return v_res_6366_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__3___redArg(
    mut v_x_6367_: *mut LeanObject,
    mut v_handle_6368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    v___x_6370_ = lean_apply_1(v_x_6367_, lean_box(0));
    if lean_obj_tag(v___x_6370_) == 0 {
        lean_dec_ref(v_handle_6368_);
        return v___x_6370_;
    } else {
        let mut v_a_6371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
        v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
        lean_inc(v_a_6371_);
        lean_dec_ref_known(v___x_6370_, 1);
        v___x_6372_ = lean_apply_2(v_handle_6368_, v_a_6371_, lean_box(0));
        return v___x_6372_;
    }
}
pub unsafe fn l_instMonadExceptOfEIO___aux__3___redArg___boxed(
    mut v_x_6373_: *mut LeanObject,
    mut v_handle_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6376_: *mut LeanObject = core::ptr::null_mut();
    v_res_6376_ = l_instMonadExceptOfEIO___aux__3___redArg(v_x_6373_, v_handle_6374_);
    return v_res_6376_;
}
pub unsafe fn l_instMonadExceptOfEIO___aux__3(
    mut v_00_u03b5_6377_: *mut LeanObject,
    mut v_00_u03b1_6378_: *mut LeanObject,
    mut v_x_6379_: *mut LeanObject,
    mut v_handle_6380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    v___x_6382_ = lean_apply_1(v_x_6379_, lean_box(0));
    if lean_obj_tag(v___x_6382_) == 0 {
        lean_dec_ref(v_handle_6380_);
        return v___x_6382_;
    } else {
        let mut v_a_6383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
        v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
        lean_inc(v_a_6383_);
        lean_dec_ref_known(v___x_6382_, 1);
        v___x_6384_ = lean_apply_2(v_handle_6380_, v_a_6383_, lean_box(0));
        return v___x_6384_;
    }
}
pub unsafe fn l_instMonadExceptOfEIO___aux__3___boxed(
    mut v_00_u03b5_6385_: *mut LeanObject,
    mut v_00_u03b1_6386_: *mut LeanObject,
    mut v_x_6387_: *mut LeanObject,
    mut v_handle_6388_: *mut LeanObject,
    mut v_a_6389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6390_: *mut LeanObject = core::ptr::null_mut();
    v_res_6390_ = l_instMonadExceptOfEIO___aux__3(
        v_00_u03b5_6385_,
        v_00_u03b1_6386_,
        v_x_6387_,
        v_handle_6388_,
    );
    return v_res_6390_;
}
pub unsafe fn l_instMonadExceptOfEIO(mut v_00_u03b5_6396_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    v___x_6397_ = l_instMonadExceptOfEIO___closed__2;
    return v___x_6397_;
}
pub unsafe fn _init_l_instOrElseEIO___closed__0() -> *mut LeanObject {
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    v___x_6398_ = l_instMonadExceptOfEIO(lean_box(0));
    return v___x_6398_;
}
pub unsafe fn _init_l_instOrElseEIO___closed__1() -> *mut LeanObject {
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    v___x_6399_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__0),
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__0_once),
        _init_l_instOrElseEIO___closed__0,
    );
    v___x_6400_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_6399_);
    return v___x_6400_;
}
pub unsafe fn _init_l_instOrElseEIO___closed__2() -> *mut LeanObject {
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    v___x_6401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__1),
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__1_once),
        _init_l_instOrElseEIO___closed__1,
    );
    v___x_6402_ = lean_alloc_closure(l_MonadExcept_orElse as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_6402_, 0, lean_box(0));
    lean_closure_set(v___x_6402_, 1, lean_box(0));
    lean_closure_set(v___x_6402_, 2, v___x_6401_);
    lean_closure_set(v___x_6402_, 3, lean_box(0));
    return v___x_6402_;
}
pub unsafe fn l_instOrElseEIO(
    mut v_00_u03b5_6403_: *mut LeanObject,
    mut v_00_u03b1_6404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    v___x_6405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__2),
        core::ptr::addr_of_mut!(l_instOrElseEIO___closed__2_once),
        _init_l_instOrElseEIO___closed__2,
    );
    return v___x_6405_;
}
pub unsafe fn l_instInhabitedEIO___aux__1___redArg(
    mut v_inst_6406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    v___x_6408_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6408_, 0, v_inst_6406_);
    return v___x_6408_;
}
pub unsafe fn l_instInhabitedEIO___aux__1___redArg___boxed(
    mut v_inst_6409_: *mut LeanObject,
    mut v_s_6410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6411_: *mut LeanObject = core::ptr::null_mut();
    v_res_6411_ = l_instInhabitedEIO___aux__1___redArg(v_inst_6409_);
    return v_res_6411_;
}
pub unsafe fn l_instInhabitedEIO___aux__1(
    mut v_00_u03b5_6412_: *mut LeanObject,
    mut v_00_u03b1_6413_: *mut LeanObject,
    mut v_inst_6414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    v___x_6416_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6416_, 0, v_inst_6414_);
    return v___x_6416_;
}
pub unsafe fn l_instInhabitedEIO___aux__1___boxed(
    mut v_00_u03b5_6417_: *mut LeanObject,
    mut v_00_u03b1_6418_: *mut LeanObject,
    mut v_inst_6419_: *mut LeanObject,
    mut v_s_6420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6421_: *mut LeanObject = core::ptr::null_mut();
    v_res_6421_ = l_instInhabitedEIO___aux__1(v_00_u03b5_6417_, v_00_u03b1_6418_, v_inst_6419_);
    return v_res_6421_;
}
pub unsafe fn l_instInhabitedEIO___redArg(mut v_inst_6422_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    v___x_6423_ = lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_6423_, 0, lean_box(0));
    lean_closure_set(v___x_6423_, 1, lean_box(0));
    lean_closure_set(v___x_6423_, 2, v_inst_6422_);
    return v___x_6423_;
}
pub unsafe fn l_instInhabitedEIO(
    mut v_00_u03b5_6424_: *mut LeanObject,
    mut v_00_u03b1_6425_: *mut LeanObject,
    mut v_inst_6426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    v___x_6427_ = lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_6427_, 0, lean_box(0));
    lean_closure_set(v___x_6427_, 1, lean_box(0));
    lean_closure_set(v___x_6427_, 2, v_inst_6426_);
    return v___x_6427_;
}
pub unsafe fn l_EIO_map___redArg(
    mut v_f_6428_: *mut LeanObject,
    mut v_x_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6435_: u8 = 0;
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6440_: u8 = 0;
    let mut v_a_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6431_ = lean_apply_1(v_x_6429_, lean_box(0));
                if lean_obj_tag(v___x_6431_) == 0 {
                    v_a_6432_ = lean_ctor_get(v___x_6431_, 0);
                    v_isSharedCheck_6440_ = (!lean_is_exclusive(v___x_6431_)) as u8;
                    if v_isSharedCheck_6440_ == 0 {
                        v___x_6434_ = v___x_6431_;
                        v_isShared_6435_ = v_isSharedCheck_6440_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6432_);
                        lean_dec(v___x_6431_);
                        v___x_6434_ = lean_box(0);
                        v_isShared_6435_ = v_isSharedCheck_6440_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_6428_);
                    v_a_6441_ = lean_ctor_get(v___x_6431_, 0);
                    v_isSharedCheck_6448_ = (!lean_is_exclusive(v___x_6431_)) as u8;
                    if v_isSharedCheck_6448_ == 0 {
                        v___x_6443_ = v___x_6431_;
                        v_isShared_6444_ = v_isSharedCheck_6448_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6441_);
                        lean_dec(v___x_6431_);
                        v___x_6443_ = lean_box(0);
                        v_isShared_6444_ = v_isSharedCheck_6448_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6436_ = lean_apply_1(v_f_6428_, v_a_6432_);
                if v_isShared_6435_ == 0 {
                    lean_ctor_set(v___x_6434_, 0, v___x_6436_);
                    v___x_6438_ = v___x_6434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6439_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6439_, 0, v___x_6436_);
                    v___x_6438_ = v_reuseFailAlloc_6439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6438_;
            }
            3 => {
                if v_isShared_6444_ == 0 {
                    v___x_6446_ = v___x_6443_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6447_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6441_);
                    v___x_6446_ = v_reuseFailAlloc_6447_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_map___redArg___boxed(
    mut v_f_6449_: *mut LeanObject,
    mut v_x_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6452_: *mut LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_EIO_map___redArg(v_f_6449_, v_x_6450_);
    return v_res_6452_;
}
pub unsafe fn l_EIO_map(
    mut v_00_u03b1_6453_: *mut LeanObject,
    mut v_00_u03b2_6454_: *mut LeanObject,
    mut v_00_u03b5_6455_: *mut LeanObject,
    mut v_f_6456_: *mut LeanObject,
    mut v_x_6457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6463_: u8 = 0;
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6468_: u8 = 0;
    let mut v_a_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6472_: u8 = 0;
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6459_ = lean_apply_1(v_x_6457_, lean_box(0));
                if lean_obj_tag(v___x_6459_) == 0 {
                    v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
                    v_isSharedCheck_6468_ = (!lean_is_exclusive(v___x_6459_)) as u8;
                    if v_isSharedCheck_6468_ == 0 {
                        v___x_6462_ = v___x_6459_;
                        v_isShared_6463_ = v_isSharedCheck_6468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6460_);
                        lean_dec(v___x_6459_);
                        v___x_6462_ = lean_box(0);
                        v_isShared_6463_ = v_isSharedCheck_6468_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_6456_);
                    v_a_6469_ = lean_ctor_get(v___x_6459_, 0);
                    v_isSharedCheck_6476_ = (!lean_is_exclusive(v___x_6459_)) as u8;
                    if v_isSharedCheck_6476_ == 0 {
                        v___x_6471_ = v___x_6459_;
                        v_isShared_6472_ = v_isSharedCheck_6476_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6469_);
                        lean_dec(v___x_6459_);
                        v___x_6471_ = lean_box(0);
                        v_isShared_6472_ = v_isSharedCheck_6476_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6464_ = lean_apply_1(v_f_6456_, v_a_6460_);
                if v_isShared_6463_ == 0 {
                    lean_ctor_set(v___x_6462_, 0, v___x_6464_);
                    v___x_6466_ = v___x_6462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6467_, 0, v___x_6464_);
                    v___x_6466_ = v_reuseFailAlloc_6467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6466_;
            }
            3 => {
                if v_isShared_6472_ == 0 {
                    v___x_6474_ = v___x_6471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
                    v___x_6474_ = v_reuseFailAlloc_6475_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_map___boxed(
    mut v_00_u03b1_6477_: *mut LeanObject,
    mut v_00_u03b2_6478_: *mut LeanObject,
    mut v_00_u03b5_6479_: *mut LeanObject,
    mut v_f_6480_: *mut LeanObject,
    mut v_x_6481_: *mut LeanObject,
    mut v_a_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6483_: *mut LeanObject = core::ptr::null_mut();
    v_res_6483_ = l_EIO_map(
        v_00_u03b1_6477_,
        v_00_u03b2_6478_,
        v_00_u03b5_6479_,
        v_f_6480_,
        v_x_6481_,
    );
    return v_res_6483_;
}
pub unsafe fn l_EIO_throw___redArg(mut v_e_6484_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    v___x_6486_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6486_, 0, v_e_6484_);
    return v___x_6486_;
}
pub unsafe fn l_EIO_throw___redArg___boxed(
    mut v_e_6487_: *mut LeanObject,
    mut v_a_6488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6489_: *mut LeanObject = core::ptr::null_mut();
    v_res_6489_ = l_EIO_throw___redArg(v_e_6487_);
    return v_res_6489_;
}
pub unsafe fn l_EIO_throw(
    mut v_00_u03b5_6490_: *mut LeanObject,
    mut v_00_u03b1_6491_: *mut LeanObject,
    mut v_e_6492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    v___x_6494_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6494_, 0, v_e_6492_);
    return v___x_6494_;
}
pub unsafe fn l_EIO_throw___boxed(
    mut v_00_u03b5_6495_: *mut LeanObject,
    mut v_00_u03b1_6496_: *mut LeanObject,
    mut v_e_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6499_: *mut LeanObject = core::ptr::null_mut();
    v_res_6499_ = l_EIO_throw(v_00_u03b5_6495_, v_00_u03b1_6496_, v_e_6497_);
    return v_res_6499_;
}
pub unsafe fn l_EIO_tryCatch___redArg(
    mut v_x_6500_: *mut LeanObject,
    mut v_handle_6501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    v___x_6503_ = lean_apply_1(v_x_6500_, lean_box(0));
    if lean_obj_tag(v___x_6503_) == 0 {
        lean_dec_ref(v_handle_6501_);
        return v___x_6503_;
    } else {
        let mut v_a_6504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
        v_a_6504_ = lean_ctor_get(v___x_6503_, 0);
        lean_inc(v_a_6504_);
        lean_dec_ref_known(v___x_6503_, 1);
        v___x_6505_ = lean_apply_2(v_handle_6501_, v_a_6504_, lean_box(0));
        return v___x_6505_;
    }
}
pub unsafe fn l_EIO_tryCatch___redArg___boxed(
    mut v_x_6506_: *mut LeanObject,
    mut v_handle_6507_: *mut LeanObject,
    mut v_a_6508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6509_: *mut LeanObject = core::ptr::null_mut();
    v_res_6509_ = l_EIO_tryCatch___redArg(v_x_6506_, v_handle_6507_);
    return v_res_6509_;
}
pub unsafe fn l_EIO_tryCatch(
    mut v_00_u03b5_6510_: *mut LeanObject,
    mut v_00_u03b1_6511_: *mut LeanObject,
    mut v_x_6512_: *mut LeanObject,
    mut v_handle_6513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    v___x_6515_ = lean_apply_1(v_x_6512_, lean_box(0));
    if lean_obj_tag(v___x_6515_) == 0 {
        lean_dec_ref(v_handle_6513_);
        return v___x_6515_;
    } else {
        let mut v_a_6516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
        v_a_6516_ = lean_ctor_get(v___x_6515_, 0);
        lean_inc(v_a_6516_);
        lean_dec_ref_known(v___x_6515_, 1);
        v___x_6517_ = lean_apply_2(v_handle_6513_, v_a_6516_, lean_box(0));
        return v___x_6517_;
    }
}
pub unsafe fn l_EIO_tryCatch___boxed(
    mut v_00_u03b5_6518_: *mut LeanObject,
    mut v_00_u03b1_6519_: *mut LeanObject,
    mut v_x_6520_: *mut LeanObject,
    mut v_handle_6521_: *mut LeanObject,
    mut v_a_6522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6523_: *mut LeanObject = core::ptr::null_mut();
    v_res_6523_ = l_EIO_tryCatch(
        v_00_u03b5_6518_,
        v_00_u03b1_6519_,
        v_x_6520_,
        v_handle_6521_,
    );
    return v_res_6523_;
}
pub unsafe fn l_EIO_ofExcept___redArg(mut v_e_6524_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_a_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_6524_) == 0 {
                    v_a_6526_ = lean_ctor_get(v_e_6524_, 0);
                    v_isSharedCheck_6533_ = (!lean_is_exclusive(v_e_6524_)) as u8;
                    if v_isSharedCheck_6533_ == 0 {
                        v___x_6528_ = v_e_6524_;
                        v_isShared_6529_ = v_isSharedCheck_6533_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6526_);
                        lean_dec(v_e_6524_);
                        v___x_6528_ = lean_box(0);
                        v_isShared_6529_ = v_isSharedCheck_6533_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6534_ = lean_ctor_get(v_e_6524_, 0);
                    v_isSharedCheck_6541_ = (!lean_is_exclusive(v_e_6524_)) as u8;
                    if v_isSharedCheck_6541_ == 0 {
                        v___x_6536_ = v_e_6524_;
                        v_isShared_6537_ = v_isSharedCheck_6541_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6534_);
                        lean_dec(v_e_6524_);
                        v___x_6536_ = lean_box(0);
                        v_isShared_6537_ = v_isSharedCheck_6541_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6529_ == 0 {
                    lean_ctor_set_tag(v___x_6528_, 1);
                    v___x_6531_ = v___x_6528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
                    v___x_6531_ = v_reuseFailAlloc_6532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6531_;
            }
            3 => {
                if v_isShared_6537_ == 0 {
                    lean_ctor_set_tag(v___x_6536_, 0);
                    v___x_6539_ = v___x_6536_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6540_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
                    v___x_6539_ = v_reuseFailAlloc_6540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_ofExcept___redArg___boxed(
    mut v_e_6542_: *mut LeanObject,
    mut v_a_6543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6544_: *mut LeanObject = core::ptr::null_mut();
    v_res_6544_ = l_EIO_ofExcept___redArg(v_e_6542_);
    return v_res_6544_;
}
pub unsafe fn l_EIO_ofExcept(
    mut v_00_u03b5_6545_: *mut LeanObject,
    mut v_00_u03b1_6546_: *mut LeanObject,
    mut v_e_6547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6552_: u8 = 0;
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6556_: u8 = 0;
    let mut v_a_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6560_: u8 = 0;
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_6547_) == 0 {
                    v_a_6549_ = lean_ctor_get(v_e_6547_, 0);
                    v_isSharedCheck_6556_ = (!lean_is_exclusive(v_e_6547_)) as u8;
                    if v_isSharedCheck_6556_ == 0 {
                        v___x_6551_ = v_e_6547_;
                        v_isShared_6552_ = v_isSharedCheck_6556_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6549_);
                        lean_dec(v_e_6547_);
                        v___x_6551_ = lean_box(0);
                        v_isShared_6552_ = v_isSharedCheck_6556_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6557_ = lean_ctor_get(v_e_6547_, 0);
                    v_isSharedCheck_6564_ = (!lean_is_exclusive(v_e_6547_)) as u8;
                    if v_isSharedCheck_6564_ == 0 {
                        v___x_6559_ = v_e_6547_;
                        v_isShared_6560_ = v_isSharedCheck_6564_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6557_);
                        lean_dec(v_e_6547_);
                        v___x_6559_ = lean_box(0);
                        v_isShared_6560_ = v_isSharedCheck_6564_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6552_ == 0 {
                    lean_ctor_set_tag(v___x_6551_, 1);
                    v___x_6554_ = v___x_6551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6555_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_a_6549_);
                    v___x_6554_ = v_reuseFailAlloc_6555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6554_;
            }
            3 => {
                if v_isShared_6560_ == 0 {
                    lean_ctor_set_tag(v___x_6559_, 0);
                    v___x_6562_ = v___x_6559_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6563_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_a_6557_);
                    v___x_6562_ = v_reuseFailAlloc_6563_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_ofExcept___boxed(
    mut v_00_u03b5_6565_: *mut LeanObject,
    mut v_00_u03b1_6566_: *mut LeanObject,
    mut v_e_6567_: *mut LeanObject,
    mut v_a_6568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6569_: *mut LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_EIO_ofExcept(v_00_u03b5_6565_, v_00_u03b1_6566_, v_e_6567_);
    return v_res_6569_;
}
pub unsafe fn l_EIO_adapt___redArg(
    mut v_f_6570_: *mut LeanObject,
    mut v_m_6571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6577_: u8 = 0;
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6581_: u8 = 0;
    let mut v_a_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6585_: u8 = 0;
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6573_ = lean_apply_1(v_m_6571_, lean_box(0));
                if lean_obj_tag(v___x_6573_) == 0 {
                    lean_dec(v_f_6570_);
                    v_a_6574_ = lean_ctor_get(v___x_6573_, 0);
                    v_isSharedCheck_6581_ = (!lean_is_exclusive(v___x_6573_)) as u8;
                    if v_isSharedCheck_6581_ == 0 {
                        v___x_6576_ = v___x_6573_;
                        v_isShared_6577_ = v_isSharedCheck_6581_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6574_);
                        lean_dec(v___x_6573_);
                        v___x_6576_ = lean_box(0);
                        v_isShared_6577_ = v_isSharedCheck_6581_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6582_ = lean_ctor_get(v___x_6573_, 0);
                    v_isSharedCheck_6590_ = (!lean_is_exclusive(v___x_6573_)) as u8;
                    if v_isSharedCheck_6590_ == 0 {
                        v___x_6584_ = v___x_6573_;
                        v_isShared_6585_ = v_isSharedCheck_6590_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6582_);
                        lean_dec(v___x_6573_);
                        v___x_6584_ = lean_box(0);
                        v_isShared_6585_ = v_isSharedCheck_6590_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6577_ == 0 {
                    v___x_6579_ = v___x_6576_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6574_);
                    v___x_6579_ = v_reuseFailAlloc_6580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6579_;
            }
            3 => {
                v___x_6586_ = lean_apply_1(v_f_6570_, v_a_6582_);
                if v_isShared_6585_ == 0 {
                    lean_ctor_set(v___x_6584_, 0, v___x_6586_);
                    v___x_6588_ = v___x_6584_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6589_, 0, v___x_6586_);
                    v___x_6588_ = v_reuseFailAlloc_6589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_adapt___redArg___boxed(
    mut v_f_6591_: *mut LeanObject,
    mut v_m_6592_: *mut LeanObject,
    mut v_s_6593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6594_: *mut LeanObject = core::ptr::null_mut();
    v_res_6594_ = l_EIO_adapt___redArg(v_f_6591_, v_m_6592_);
    return v_res_6594_;
}
pub unsafe fn l_EIO_adapt(
    mut v_00_u03b5_6595_: *mut LeanObject,
    mut v_00_u03b5_x27_6596_: *mut LeanObject,
    mut v_00_u03b1_6597_: *mut LeanObject,
    mut v_f_6598_: *mut LeanObject,
    mut v_m_6599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6605_: u8 = 0;
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v_a_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6613_: u8 = 0;
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6601_ = lean_apply_1(v_m_6599_, lean_box(0));
                if lean_obj_tag(v___x_6601_) == 0 {
                    lean_dec(v_f_6598_);
                    v_a_6602_ = lean_ctor_get(v___x_6601_, 0);
                    v_isSharedCheck_6609_ = (!lean_is_exclusive(v___x_6601_)) as u8;
                    if v_isSharedCheck_6609_ == 0 {
                        v___x_6604_ = v___x_6601_;
                        v_isShared_6605_ = v_isSharedCheck_6609_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6602_);
                        lean_dec(v___x_6601_);
                        v___x_6604_ = lean_box(0);
                        v_isShared_6605_ = v_isSharedCheck_6609_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6610_ = lean_ctor_get(v___x_6601_, 0);
                    v_isSharedCheck_6618_ = (!lean_is_exclusive(v___x_6601_)) as u8;
                    if v_isSharedCheck_6618_ == 0 {
                        v___x_6612_ = v___x_6601_;
                        v_isShared_6613_ = v_isSharedCheck_6618_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6610_);
                        lean_dec(v___x_6601_);
                        v___x_6612_ = lean_box(0);
                        v_isShared_6613_ = v_isSharedCheck_6618_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6605_ == 0 {
                    v___x_6607_ = v___x_6604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6608_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6608_, 0, v_a_6602_);
                    v___x_6607_ = v_reuseFailAlloc_6608_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6607_;
            }
            3 => {
                v___x_6614_ = lean_apply_1(v_f_6598_, v_a_6610_);
                if v_isShared_6613_ == 0 {
                    lean_ctor_set(v___x_6612_, 0, v___x_6614_);
                    v___x_6616_ = v___x_6612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6617_, 0, v___x_6614_);
                    v___x_6616_ = v_reuseFailAlloc_6617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_adapt___boxed(
    mut v_00_u03b5_6619_: *mut LeanObject,
    mut v_00_u03b5_x27_6620_: *mut LeanObject,
    mut v_00_u03b1_6621_: *mut LeanObject,
    mut v_f_6622_: *mut LeanObject,
    mut v_m_6623_: *mut LeanObject,
    mut v_s_6624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6625_: *mut LeanObject = core::ptr::null_mut();
    v_res_6625_ = l_EIO_adapt(
        v_00_u03b5_6619_,
        v_00_u03b5_x27_6620_,
        v_00_u03b1_6621_,
        v_f_6622_,
        v_m_6623_,
    );
    return v_res_6625_;
}
pub unsafe fn l_EIO_adaptExcept___redArg(
    mut v_f_6626_: *mut LeanObject,
    mut v_m_6627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6637_: u8 = 0;
    let mut v_a_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6641_: u8 = 0;
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6629_ = lean_apply_1(v_m_6627_, lean_box(0));
                if lean_obj_tag(v___x_6629_) == 0 {
                    lean_dec(v_f_6626_);
                    v_a_6630_ = lean_ctor_get(v___x_6629_, 0);
                    v_isSharedCheck_6637_ = (!lean_is_exclusive(v___x_6629_)) as u8;
                    if v_isSharedCheck_6637_ == 0 {
                        v___x_6632_ = v___x_6629_;
                        v_isShared_6633_ = v_isSharedCheck_6637_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6630_);
                        lean_dec(v___x_6629_);
                        v___x_6632_ = lean_box(0);
                        v_isShared_6633_ = v_isSharedCheck_6637_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6638_ = lean_ctor_get(v___x_6629_, 0);
                    v_isSharedCheck_6646_ = (!lean_is_exclusive(v___x_6629_)) as u8;
                    if v_isSharedCheck_6646_ == 0 {
                        v___x_6640_ = v___x_6629_;
                        v_isShared_6641_ = v_isSharedCheck_6646_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6638_);
                        lean_dec(v___x_6629_);
                        v___x_6640_ = lean_box(0);
                        v_isShared_6641_ = v_isSharedCheck_6646_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6633_ == 0 {
                    v___x_6635_ = v___x_6632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6636_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6636_, 0, v_a_6630_);
                    v___x_6635_ = v_reuseFailAlloc_6636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6635_;
            }
            3 => {
                v___x_6642_ = lean_apply_1(v_f_6626_, v_a_6638_);
                if v_isShared_6641_ == 0 {
                    lean_ctor_set(v___x_6640_, 0, v___x_6642_);
                    v___x_6644_ = v___x_6640_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6645_, 0, v___x_6642_);
                    v___x_6644_ = v_reuseFailAlloc_6645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_adaptExcept___redArg___boxed(
    mut v_f_6647_: *mut LeanObject,
    mut v_m_6648_: *mut LeanObject,
    mut v_a_6649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6650_: *mut LeanObject = core::ptr::null_mut();
    v_res_6650_ = l_EIO_adaptExcept___redArg(v_f_6647_, v_m_6648_);
    return v_res_6650_;
}
pub unsafe fn l_EIO_adaptExcept(
    mut v_00_u03b5_6651_: *mut LeanObject,
    mut v_00_u03b5_x27_6652_: *mut LeanObject,
    mut v_00_u03b1_6653_: *mut LeanObject,
    mut v_f_6654_: *mut LeanObject,
    mut v_m_6655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6661_: u8 = 0;
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6665_: u8 = 0;
    let mut v_a_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6657_ = lean_apply_1(v_m_6655_, lean_box(0));
                if lean_obj_tag(v___x_6657_) == 0 {
                    lean_dec(v_f_6654_);
                    v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
                    v_isSharedCheck_6665_ = (!lean_is_exclusive(v___x_6657_)) as u8;
                    if v_isSharedCheck_6665_ == 0 {
                        v___x_6660_ = v___x_6657_;
                        v_isShared_6661_ = v_isSharedCheck_6665_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6658_);
                        lean_dec(v___x_6657_);
                        v___x_6660_ = lean_box(0);
                        v_isShared_6661_ = v_isSharedCheck_6665_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6666_ = lean_ctor_get(v___x_6657_, 0);
                    v_isSharedCheck_6674_ = (!lean_is_exclusive(v___x_6657_)) as u8;
                    if v_isSharedCheck_6674_ == 0 {
                        v___x_6668_ = v___x_6657_;
                        v_isShared_6669_ = v_isSharedCheck_6674_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6666_);
                        lean_dec(v___x_6657_);
                        v___x_6668_ = lean_box(0);
                        v_isShared_6669_ = v_isSharedCheck_6674_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6661_ == 0 {
                    v___x_6663_ = v___x_6660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6658_);
                    v___x_6663_ = v_reuseFailAlloc_6664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6663_;
            }
            3 => {
                v___x_6670_ = lean_apply_1(v_f_6654_, v_a_6666_);
                if v_isShared_6669_ == 0 {
                    lean_ctor_set(v___x_6668_, 0, v___x_6670_);
                    v___x_6672_ = v___x_6668_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6673_, 0, v___x_6670_);
                    v___x_6672_ = v_reuseFailAlloc_6673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_adaptExcept___boxed(
    mut v_00_u03b5_6675_: *mut LeanObject,
    mut v_00_u03b5_x27_6676_: *mut LeanObject,
    mut v_00_u03b1_6677_: *mut LeanObject,
    mut v_f_6678_: *mut LeanObject,
    mut v_m_6679_: *mut LeanObject,
    mut v_a_6680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6681_: *mut LeanObject = core::ptr::null_mut();
    v_res_6681_ = l_EIO_adaptExcept(
        v_00_u03b5_6675_,
        v_00_u03b5_x27_6676_,
        v_00_u03b1_6677_,
        v_f_6678_,
        v_m_6679_,
    );
    return v_res_6681_;
}
pub unsafe fn l_BaseIO_toIO___redArg(mut v_act_6682_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    v___x_6684_ = lean_apply_1(v_act_6682_, lean_box(0));
    v___x_6685_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6685_, 0, v___x_6684_);
    return v___x_6685_;
}
pub unsafe fn l_BaseIO_toIO___redArg___boxed(
    mut v_act_6686_: *mut LeanObject,
    mut v_a_6687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6688_: *mut LeanObject = core::ptr::null_mut();
    v_res_6688_ = l_BaseIO_toIO___redArg(v_act_6686_);
    return v_res_6688_;
}
pub unsafe fn l_BaseIO_toIO(
    mut v_00_u03b1_6689_: *mut LeanObject,
    mut v_act_6690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    v___x_6692_ = lean_apply_1(v_act_6690_, lean_box(0));
    v___x_6693_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6693_, 0, v___x_6692_);
    return v___x_6693_;
}
pub unsafe fn l_BaseIO_toIO___boxed(
    mut v_00_u03b1_6694_: *mut LeanObject,
    mut v_act_6695_: *mut LeanObject,
    mut v_a_6696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6697_: *mut LeanObject = core::ptr::null_mut();
    v_res_6697_ = l_BaseIO_toIO(v_00_u03b1_6694_, v_act_6695_);
    return v_res_6697_;
}
pub unsafe fn l_EIO_toIO___redArg(
    mut v_f_6698_: *mut LeanObject,
    mut v_act_6699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6705_: u8 = 0;
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6709_: u8 = 0;
    let mut v_a_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6713_: u8 = 0;
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6701_ = lean_apply_1(v_act_6699_, lean_box(0));
                if lean_obj_tag(v___x_6701_) == 0 {
                    lean_dec_ref(v_f_6698_);
                    v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
                    v_isSharedCheck_6709_ = (!lean_is_exclusive(v___x_6701_)) as u8;
                    if v_isSharedCheck_6709_ == 0 {
                        v___x_6704_ = v___x_6701_;
                        v_isShared_6705_ = v_isSharedCheck_6709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6702_);
                        lean_dec(v___x_6701_);
                        v___x_6704_ = lean_box(0);
                        v_isShared_6705_ = v_isSharedCheck_6709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6710_ = lean_ctor_get(v___x_6701_, 0);
                    v_isSharedCheck_6718_ = (!lean_is_exclusive(v___x_6701_)) as u8;
                    if v_isSharedCheck_6718_ == 0 {
                        v___x_6712_ = v___x_6701_;
                        v_isShared_6713_ = v_isSharedCheck_6718_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6710_);
                        lean_dec(v___x_6701_);
                        v___x_6712_ = lean_box(0);
                        v_isShared_6713_ = v_isSharedCheck_6718_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6705_ == 0 {
                    v___x_6707_ = v___x_6704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6708_, 0, v_a_6702_);
                    v___x_6707_ = v_reuseFailAlloc_6708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6707_;
            }
            3 => {
                v___x_6714_ = lean_apply_1(v_f_6698_, v_a_6710_);
                if v_isShared_6713_ == 0 {
                    lean_ctor_set(v___x_6712_, 0, v___x_6714_);
                    v___x_6716_ = v___x_6712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6717_, 0, v___x_6714_);
                    v___x_6716_ = v_reuseFailAlloc_6717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toIO___redArg___boxed(
    mut v_f_6719_: *mut LeanObject,
    mut v_act_6720_: *mut LeanObject,
    mut v_a_6721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6722_: *mut LeanObject = core::ptr::null_mut();
    v_res_6722_ = l_EIO_toIO___redArg(v_f_6719_, v_act_6720_);
    return v_res_6722_;
}
pub unsafe fn l_EIO_toIO(
    mut v_00_u03b5_6723_: *mut LeanObject,
    mut v_00_u03b1_6724_: *mut LeanObject,
    mut v_f_6725_: *mut LeanObject,
    mut v_act_6726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6732_: u8 = 0;
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6736_: u8 = 0;
    let mut v_a_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6740_: u8 = 0;
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6728_ = lean_apply_1(v_act_6726_, lean_box(0));
                if lean_obj_tag(v___x_6728_) == 0 {
                    lean_dec_ref(v_f_6725_);
                    v_a_6729_ = lean_ctor_get(v___x_6728_, 0);
                    v_isSharedCheck_6736_ = (!lean_is_exclusive(v___x_6728_)) as u8;
                    if v_isSharedCheck_6736_ == 0 {
                        v___x_6731_ = v___x_6728_;
                        v_isShared_6732_ = v_isSharedCheck_6736_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6729_);
                        lean_dec(v___x_6728_);
                        v___x_6731_ = lean_box(0);
                        v_isShared_6732_ = v_isSharedCheck_6736_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6737_ = lean_ctor_get(v___x_6728_, 0);
                    v_isSharedCheck_6745_ = (!lean_is_exclusive(v___x_6728_)) as u8;
                    if v_isSharedCheck_6745_ == 0 {
                        v___x_6739_ = v___x_6728_;
                        v_isShared_6740_ = v_isSharedCheck_6745_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6737_);
                        lean_dec(v___x_6728_);
                        v___x_6739_ = lean_box(0);
                        v_isShared_6740_ = v_isSharedCheck_6745_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6732_ == 0 {
                    v___x_6734_ = v___x_6731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6735_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_a_6729_);
                    v___x_6734_ = v_reuseFailAlloc_6735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6734_;
            }
            3 => {
                v___x_6741_ = lean_apply_1(v_f_6725_, v_a_6737_);
                if v_isShared_6740_ == 0 {
                    lean_ctor_set(v___x_6739_, 0, v___x_6741_);
                    v___x_6743_ = v___x_6739_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6744_, 0, v___x_6741_);
                    v___x_6743_ = v_reuseFailAlloc_6744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toIO___boxed(
    mut v_00_u03b5_6746_: *mut LeanObject,
    mut v_00_u03b1_6747_: *mut LeanObject,
    mut v_f_6748_: *mut LeanObject,
    mut v_act_6749_: *mut LeanObject,
    mut v_a_6750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6751_: *mut LeanObject = core::ptr::null_mut();
    v_res_6751_ = l_EIO_toIO(v_00_u03b5_6746_, v_00_u03b1_6747_, v_f_6748_, v_act_6749_);
    return v_res_6751_;
}
pub unsafe fn l_EIO_toIO_x27___redArg(mut v_act_6752_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6758_: u8 = 0;
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6763_: u8 = 0;
    let mut v_a_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6767_: u8 = 0;
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6754_ = lean_apply_1(v_act_6752_, lean_box(0));
                if lean_obj_tag(v___x_6754_) == 0 {
                    v_a_6755_ = lean_ctor_get(v___x_6754_, 0);
                    v_isSharedCheck_6763_ = (!lean_is_exclusive(v___x_6754_)) as u8;
                    if v_isSharedCheck_6763_ == 0 {
                        v___x_6757_ = v___x_6754_;
                        v_isShared_6758_ = v_isSharedCheck_6763_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6755_);
                        lean_dec(v___x_6754_);
                        v___x_6757_ = lean_box(0);
                        v_isShared_6758_ = v_isSharedCheck_6763_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6764_ = lean_ctor_get(v___x_6754_, 0);
                    v_isSharedCheck_6772_ = (!lean_is_exclusive(v___x_6754_)) as u8;
                    if v_isSharedCheck_6772_ == 0 {
                        v___x_6766_ = v___x_6754_;
                        v_isShared_6767_ = v_isSharedCheck_6772_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6764_);
                        lean_dec(v___x_6754_);
                        v___x_6766_ = lean_box(0);
                        v_isShared_6767_ = v_isSharedCheck_6772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6759_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6759_, 0, v_a_6755_);
                if v_isShared_6758_ == 0 {
                    lean_ctor_set(v___x_6757_, 0, v___x_6759_);
                    v___x_6761_ = v___x_6757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6762_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6762_, 0, v___x_6759_);
                    v___x_6761_ = v_reuseFailAlloc_6762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6761_;
            }
            3 => {
                v___x_6768_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6768_, 0, v_a_6764_);
                if v_isShared_6767_ == 0 {
                    lean_ctor_set_tag(v___x_6766_, 0);
                    lean_ctor_set(v___x_6766_, 0, v___x_6768_);
                    v___x_6770_ = v___x_6766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6771_, 0, v___x_6768_);
                    v___x_6770_ = v_reuseFailAlloc_6771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toIO_x27___redArg___boxed(
    mut v_act_6773_: *mut LeanObject,
    mut v_a_6774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6775_: *mut LeanObject = core::ptr::null_mut();
    v_res_6775_ = l_EIO_toIO_x27___redArg(v_act_6773_);
    return v_res_6775_;
}
pub unsafe fn l_EIO_toIO_x27(
    mut v_00_u03b5_6776_: *mut LeanObject,
    mut v_00_u03b1_6777_: *mut LeanObject,
    mut v_act_6778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6789_: u8 = 0;
    let mut v_a_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6793_: u8 = 0;
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6780_ = lean_apply_1(v_act_6778_, lean_box(0));
                if lean_obj_tag(v___x_6780_) == 0 {
                    v_a_6781_ = lean_ctor_get(v___x_6780_, 0);
                    v_isSharedCheck_6789_ = (!lean_is_exclusive(v___x_6780_)) as u8;
                    if v_isSharedCheck_6789_ == 0 {
                        v___x_6783_ = v___x_6780_;
                        v_isShared_6784_ = v_isSharedCheck_6789_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6781_);
                        lean_dec(v___x_6780_);
                        v___x_6783_ = lean_box(0);
                        v_isShared_6784_ = v_isSharedCheck_6789_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6790_ = lean_ctor_get(v___x_6780_, 0);
                    v_isSharedCheck_6798_ = (!lean_is_exclusive(v___x_6780_)) as u8;
                    if v_isSharedCheck_6798_ == 0 {
                        v___x_6792_ = v___x_6780_;
                        v_isShared_6793_ = v_isSharedCheck_6798_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6790_);
                        lean_dec(v___x_6780_);
                        v___x_6792_ = lean_box(0);
                        v_isShared_6793_ = v_isSharedCheck_6798_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6785_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6785_, 0, v_a_6781_);
                if v_isShared_6784_ == 0 {
                    lean_ctor_set(v___x_6783_, 0, v___x_6785_);
                    v___x_6787_ = v___x_6783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6788_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6788_, 0, v___x_6785_);
                    v___x_6787_ = v_reuseFailAlloc_6788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6787_;
            }
            3 => {
                v___x_6794_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6794_, 0, v_a_6790_);
                if v_isShared_6793_ == 0 {
                    lean_ctor_set_tag(v___x_6792_, 0);
                    lean_ctor_set(v___x_6792_, 0, v___x_6794_);
                    v___x_6796_ = v___x_6792_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6797_, 0, v___x_6794_);
                    v___x_6796_ = v_reuseFailAlloc_6797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_toIO_x27___boxed(
    mut v_00_u03b5_6799_: *mut LeanObject,
    mut v_00_u03b1_6800_: *mut LeanObject,
    mut v_act_6801_: *mut LeanObject,
    mut v_a_6802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6803_: *mut LeanObject = core::ptr::null_mut();
    v_res_6803_ = l_EIO_toIO_x27(v_00_u03b5_6799_, v_00_u03b1_6800_, v_act_6801_);
    return v_res_6803_;
}
pub unsafe fn l_IO_toEIO___redArg(
    mut v_f_6804_: *mut LeanObject,
    mut v_act_6805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6811_: u8 = 0;
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6815_: u8 = 0;
    let mut v_a_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6819_: u8 = 0;
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6807_ = lean_apply_1(v_act_6805_, lean_box(0));
                if lean_obj_tag(v___x_6807_) == 0 {
                    lean_dec(v_f_6804_);
                    v_a_6808_ = lean_ctor_get(v___x_6807_, 0);
                    v_isSharedCheck_6815_ = (!lean_is_exclusive(v___x_6807_)) as u8;
                    if v_isSharedCheck_6815_ == 0 {
                        v___x_6810_ = v___x_6807_;
                        v_isShared_6811_ = v_isSharedCheck_6815_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6808_);
                        lean_dec(v___x_6807_);
                        v___x_6810_ = lean_box(0);
                        v_isShared_6811_ = v_isSharedCheck_6815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6816_ = lean_ctor_get(v___x_6807_, 0);
                    v_isSharedCheck_6824_ = (!lean_is_exclusive(v___x_6807_)) as u8;
                    if v_isSharedCheck_6824_ == 0 {
                        v___x_6818_ = v___x_6807_;
                        v_isShared_6819_ = v_isSharedCheck_6824_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6816_);
                        lean_dec(v___x_6807_);
                        v___x_6818_ = lean_box(0);
                        v_isShared_6819_ = v_isSharedCheck_6824_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6811_ == 0 {
                    v___x_6813_ = v___x_6810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6814_, 0, v_a_6808_);
                    v___x_6813_ = v_reuseFailAlloc_6814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6813_;
            }
            3 => {
                v___x_6820_ = lean_apply_1(v_f_6804_, v_a_6816_);
                if v_isShared_6819_ == 0 {
                    lean_ctor_set(v___x_6818_, 0, v___x_6820_);
                    v___x_6822_ = v___x_6818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6823_, 0, v___x_6820_);
                    v___x_6822_ = v_reuseFailAlloc_6823_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_toEIO___redArg___boxed(
    mut v_f_6825_: *mut LeanObject,
    mut v_act_6826_: *mut LeanObject,
    mut v_a_6827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6828_: *mut LeanObject = core::ptr::null_mut();
    v_res_6828_ = l_IO_toEIO___redArg(v_f_6825_, v_act_6826_);
    return v_res_6828_;
}
pub unsafe fn l_IO_toEIO(
    mut v_00_u03b5_6829_: *mut LeanObject,
    mut v_00_u03b1_6830_: *mut LeanObject,
    mut v_f_6831_: *mut LeanObject,
    mut v_act_6832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut v_a_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6846_: u8 = 0;
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6834_ = lean_apply_1(v_act_6832_, lean_box(0));
                if lean_obj_tag(v___x_6834_) == 0 {
                    lean_dec(v_f_6831_);
                    v_a_6835_ = lean_ctor_get(v___x_6834_, 0);
                    v_isSharedCheck_6842_ = (!lean_is_exclusive(v___x_6834_)) as u8;
                    if v_isSharedCheck_6842_ == 0 {
                        v___x_6837_ = v___x_6834_;
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6835_);
                        lean_dec(v___x_6834_);
                        v___x_6837_ = lean_box(0);
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6843_ = lean_ctor_get(v___x_6834_, 0);
                    v_isSharedCheck_6851_ = (!lean_is_exclusive(v___x_6834_)) as u8;
                    if v_isSharedCheck_6851_ == 0 {
                        v___x_6845_ = v___x_6834_;
                        v_isShared_6846_ = v_isSharedCheck_6851_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6843_);
                        lean_dec(v___x_6834_);
                        v___x_6845_ = lean_box(0);
                        v_isShared_6846_ = v_isSharedCheck_6851_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6838_ == 0 {
                    v___x_6840_ = v___x_6837_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6841_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
                    v___x_6840_ = v_reuseFailAlloc_6841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6840_;
            }
            3 => {
                v___x_6847_ = lean_apply_1(v_f_6831_, v_a_6843_);
                if v_isShared_6846_ == 0 {
                    lean_ctor_set(v___x_6845_, 0, v___x_6847_);
                    v___x_6849_ = v___x_6845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6850_, 0, v___x_6847_);
                    v___x_6849_ = v_reuseFailAlloc_6850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_toEIO___boxed(
    mut v_00_u03b5_6852_: *mut LeanObject,
    mut v_00_u03b1_6853_: *mut LeanObject,
    mut v_f_6854_: *mut LeanObject,
    mut v_act_6855_: *mut LeanObject,
    mut v_a_6856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6857_: *mut LeanObject = core::ptr::null_mut();
    v_res_6857_ = l_IO_toEIO(v_00_u03b5_6852_, v_00_u03b1_6853_, v_f_6854_, v_act_6855_);
    return v_res_6857_;
}
pub unsafe fn l_unsafeBaseIO___redArg(mut v_fn_6858_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    v___x_6859_ = lean_box(0);
    v___x_6860_ = lean_apply_1(v_fn_6858_, v___x_6859_);
    return v___x_6860_;
}
pub unsafe fn l_unsafeBaseIO(
    mut v_00_u03b1_6861_: *mut LeanObject,
    mut v_fn_6862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    v___x_6863_ = l_unsafeBaseIO___redArg(v_fn_6862_);
    return v___x_6863_;
}
pub unsafe fn l_unsafeEIO___redArg(mut v_fn_6864_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    v___x_6865_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6865_, 0, lean_box(0));
    lean_closure_set(v___x_6865_, 1, lean_box(0));
    lean_closure_set(v___x_6865_, 2, v_fn_6864_);
    v___x_6866_ = l_unsafeBaseIO___redArg(v___x_6865_);
    return v___x_6866_;
}
pub unsafe fn l_unsafeEIO(
    mut v_00_u03b5_6867_: *mut LeanObject,
    mut v_00_u03b1_6868_: *mut LeanObject,
    mut v_fn_6869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    v___x_6870_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6870_, 0, lean_box(0));
    lean_closure_set(v___x_6870_, 1, lean_box(0));
    lean_closure_set(v___x_6870_, 2, v_fn_6869_);
    v___x_6871_ = l_unsafeBaseIO___redArg(v___x_6870_);
    return v___x_6871_;
}
pub unsafe fn l_unsafeIO___redArg(mut v_fn_6872_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    v___x_6873_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6873_, 0, lean_box(0));
    lean_closure_set(v___x_6873_, 1, lean_box(0));
    lean_closure_set(v___x_6873_, 2, v_fn_6872_);
    v___x_6874_ = l_unsafeBaseIO___redArg(v___x_6873_);
    return v___x_6874_;
}
pub unsafe fn l_unsafeIO(
    mut v_00_u03b1_6875_: *mut LeanObject,
    mut v_fn_6876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    v___x_6877_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6877_, 0, lean_box(0));
    lean_closure_set(v___x_6877_, 1, lean_box(0));
    lean_closure_set(v___x_6877_, 2, v_fn_6876_);
    v___x_6878_ = l_unsafeBaseIO___redArg(v___x_6877_);
    return v___x_6878_;
}
pub unsafe fn l_timeit___boxed(
    mut v_00_u03b1_6883_: *mut LeanObject,
    mut v_msg_6884_: *mut LeanObject,
    mut v_fn_6885_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6887_: *mut LeanObject = core::ptr::null_mut();
    v_res_6887_ = lean_io_timeit(v_msg_6884_, v_fn_6885_);
    lean_dec_ref(v_msg_6884_);
    return v_res_6887_;
}
pub unsafe fn l_allocprof___boxed(
    mut v_00_u03b1_6892_: *mut LeanObject,
    mut v_msg_6893_: *mut LeanObject,
    mut v_fn_6894_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6896_: *mut LeanObject = core::ptr::null_mut();
    v_res_6896_ = lean_io_allocprof(v_msg_6893_, v_fn_6894_);
    lean_dec_ref(v_msg_6893_);
    return v_res_6896_;
}
pub unsafe fn l_IO_initializing___boxed(
    mut v_a_00___x40___internal___hyg_6898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6899_: u8 = 0;
    let mut v_r_6900_: *mut LeanObject = core::ptr::null_mut();
    v_res_6899_ = lean_io_initializing();
    v_r_6900_ = lean_box((v_res_6899_) as usize);
    return v_r_6900_;
}
pub unsafe fn l_BaseIO_asTask___boxed(
    mut v_00_u03b1_6905_: *mut LeanObject,
    mut v_act_6906_: *mut LeanObject,
    mut v_prio_6907_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6909_: *mut LeanObject = core::ptr::null_mut();
    v_res_6909_ = lean_io_as_task(v_act_6906_, v_prio_6907_);
    return v_res_6909_;
}
pub unsafe fn l_BaseIO_mapTask___boxed(
    mut v_00_u03b1_6917_: *mut LeanObject,
    mut v_00_u03b2_6918_: *mut LeanObject,
    mut v_f_6919_: *mut LeanObject,
    mut v_t_6920_: *mut LeanObject,
    mut v_prio_6921_: *mut LeanObject,
    mut v_sync_6922_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6924_: u8 = 0;
    let mut v_res_6925_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6924_ = (lean_unbox(v_sync_6922_) as u8);
    v_res_6925_ = lean_io_map_task(v_f_6919_, v_t_6920_, v_prio_6921_, v_sync_boxed_6924_);
    return v_res_6925_;
}
pub unsafe fn l_BaseIO_bindTask___boxed(
    mut v_00_u03b1_6933_: *mut LeanObject,
    mut v_00_u03b2_6934_: *mut LeanObject,
    mut v_t_6935_: *mut LeanObject,
    mut v_f_6936_: *mut LeanObject,
    mut v_prio_6937_: *mut LeanObject,
    mut v_sync_6938_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6940_: u8 = 0;
    let mut v_res_6941_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6940_ = (lean_unbox(v_sync_6938_) as u8);
    v_res_6941_ = lean_io_bind_task(v_t_6935_, v_f_6936_, v_prio_6937_, v_sync_boxed_6940_);
    return v_res_6941_;
}
pub unsafe fn l_BaseIO_chainTask___redArg(
    mut v_t_6942_: *mut LeanObject,
    mut v_f_6943_: *mut LeanObject,
    mut v_prio_6944_: *mut LeanObject,
    mut v_sync_6945_: u8,
) -> *mut LeanObject {
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    v___x_6947_ = lean_io_map_task(v_f_6943_, v_t_6942_, v_prio_6944_, v_sync_6945_);
    lean_dec_ref(v___x_6947_);
    v___x_6948_ = lean_box(0);
    return v___x_6948_;
}
pub unsafe fn l_BaseIO_chainTask___redArg___boxed(
    mut v_t_6949_: *mut LeanObject,
    mut v_f_6950_: *mut LeanObject,
    mut v_prio_6951_: *mut LeanObject,
    mut v_sync_6952_: *mut LeanObject,
    mut v_a_6953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6954_: u8 = 0;
    let mut v_res_6955_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6954_ = (lean_unbox(v_sync_6952_) as u8);
    v_res_6955_ =
        l_BaseIO_chainTask___redArg(v_t_6949_, v_f_6950_, v_prio_6951_, v_sync_boxed_6954_);
    return v_res_6955_;
}
pub unsafe fn l_BaseIO_chainTask(
    mut v_00_u03b1_6956_: *mut LeanObject,
    mut v_t_6957_: *mut LeanObject,
    mut v_f_6958_: *mut LeanObject,
    mut v_prio_6959_: *mut LeanObject,
    mut v_sync_6960_: u8,
) -> *mut LeanObject {
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    v___x_6962_ = l_BaseIO_chainTask___redArg(v_t_6957_, v_f_6958_, v_prio_6959_, v_sync_6960_);
    return v___x_6962_;
}
pub unsafe fn l_BaseIO_chainTask___boxed(
    mut v_00_u03b1_6963_: *mut LeanObject,
    mut v_t_6964_: *mut LeanObject,
    mut v_f_6965_: *mut LeanObject,
    mut v_prio_6966_: *mut LeanObject,
    mut v_sync_6967_: *mut LeanObject,
    mut v_a_6968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6969_: u8 = 0;
    let mut v_res_6970_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6969_ = (lean_unbox(v_sync_6967_) as u8);
    v_res_6970_ = l_BaseIO_chainTask(
        v_00_u03b1_6963_,
        v_t_6964_,
        v_f_6965_,
        v_prio_6966_,
        v_sync_boxed_6969_,
    );
    return v_res_6970_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(
    mut v_x_6971_: *mut LeanObject,
    mut v_f_6972_: *mut LeanObject,
    mut v_a_6973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    v___x_6975_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6975_, 0, v_a_6973_);
    lean_ctor_set(v___x_6975_, 1, v_x_6971_);
    v___x_6976_ = l_List_reverse___redArg(v___x_6975_);
    v___x_6977_ = lean_apply_2(v_f_6972_, v___x_6976_, lean_box(0));
    return v___x_6977_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(
    mut v_x_6978_: *mut LeanObject,
    mut v_f_6979_: *mut LeanObject,
    mut v_a_6980_: *mut LeanObject,
    mut v___y_6981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6982_: *mut LeanObject = core::ptr::null_mut();
    v_res_6982_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(
        v_x_6978_, v_f_6979_, v_a_6980_,
    );
    return v_res_6982_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(
    mut v_x_6983_: *mut LeanObject,
    mut v_f_6984_: *mut LeanObject,
    mut v_prio_6985_: *mut LeanObject,
    mut v_sync_6986_: *mut LeanObject,
    mut v_tail_6987_: *mut LeanObject,
    mut v_a_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6990_: u8 = 0;
    let mut v_res_6991_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6990_ = (lean_unbox(v_sync_6986_) as u8);
    v_res_6991_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(
        v_x_6983_,
        v_f_6984_,
        v_prio_6985_,
        v_sync_boxed_6990_,
        v_tail_6987_,
        v_a_6988_,
    );
    return v_res_6991_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(
    mut v_f_6992_: *mut LeanObject,
    mut v_prio_6993_: *mut LeanObject,
    mut v_sync_6994_: u8,
    mut v_x_6995_: *mut LeanObject,
    mut v_x_6996_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6995_) == 0 {
        if v_sync_6994_ == 0 {
            let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
            v___x_6998_ = l_List_reverse___redArg(v_x_6996_);
            v___x_6999_ = lean_apply_1(v_f_6992_, v___x_6998_);
            v___x_7000_ = lean_io_as_task(v___x_6999_, v_prio_6993_);
            return v___x_7000_;
        } else {
            let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_prio_6993_);
            v___x_7001_ = l_List_reverse___redArg(v_x_6996_);
            v___x_7002_ = lean_apply_2(v_f_6992_, v___x_7001_, lean_box(0));
            v___x_7003_ = lean_task_pure(v___x_7002_);
            return v___x_7003_;
        }
    } else {
        let mut v_tail_7004_: *mut LeanObject = core::ptr::null_mut();
        v_tail_7004_ = lean_ctor_get(v_x_6995_, 1);
        if lean_obj_tag(v_tail_7004_) == 0 {
            let mut v_head_7005_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_7006_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
            v_head_7005_ = lean_ctor_get(v_x_6995_, 0);
            lean_inc(v_head_7005_);
            lean_dec_ref_known(v_x_6995_, 2);
            v___f_7006_ = lean_alloc_closure(
                l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_7006_, 0, v_x_6996_);
            lean_closure_set(v___f_7006_, 1, v_f_6992_);
            v___x_7007_ = lean_io_map_task(v___f_7006_, v_head_7005_, v_prio_6993_, v_sync_6994_);
            return v___x_7007_;
        } else {
            let mut v_head_7008_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_7010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_7004_);
            v_head_7008_ = lean_ctor_get(v_x_6995_, 0);
            lean_inc(v_head_7008_);
            lean_dec_ref_known(v_x_6995_, 2);
            v___x_7009_ = lean_box((v_sync_6994_) as usize);
            lean_inc(v_prio_6993_);
            v___f_7010_ = lean_alloc_closure(
                l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                7,
                5,
            );
            lean_closure_set(v___f_7010_, 0, v_x_6996_);
            lean_closure_set(v___f_7010_, 1, v_f_6992_);
            lean_closure_set(v___f_7010_, 2, v_prio_6993_);
            lean_closure_set(v___f_7010_, 3, v___x_7009_);
            lean_closure_set(v___f_7010_, 4, v_tail_7004_);
            v___x_7011_ = lean_io_bind_task(v_head_7008_, v___f_7010_, v_prio_6993_, v_sync_6994_);
            return v___x_7011_;
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(
    mut v_x_7012_: *mut LeanObject,
    mut v_f_7013_: *mut LeanObject,
    mut v_prio_7014_: *mut LeanObject,
    mut v_sync_7015_: u8,
    mut v_tail_7016_: *mut LeanObject,
    mut v_a_7017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut LeanObject = core::ptr::null_mut();
    v___x_7019_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_7019_, 0, v_a_7017_);
    lean_ctor_set(v___x_7019_, 1, v_x_7012_);
    v___x_7020_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(
        v_f_7013_,
        v_prio_7014_,
        v_sync_7015_,
        v_tail_7016_,
        v___x_7019_,
    );
    return v___x_7020_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(
    mut v_f_7021_: *mut LeanObject,
    mut v_prio_7022_: *mut LeanObject,
    mut v_sync_7023_: *mut LeanObject,
    mut v_x_7024_: *mut LeanObject,
    mut v_x_7025_: *mut LeanObject,
    mut v_a_7026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7027_: u8 = 0;
    let mut v_res_7028_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7027_ = (lean_unbox(v_sync_7023_) as u8);
    v_res_7028_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(
        v_f_7021_,
        v_prio_7022_,
        v_sync_boxed_7027_,
        v_x_7024_,
        v_x_7025_,
    );
    return v_res_7028_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go(
    mut v_00_u03b1_7029_: *mut LeanObject,
    mut v_00_u03b2_7030_: *mut LeanObject,
    mut v_f_7031_: *mut LeanObject,
    mut v_prio_7032_: *mut LeanObject,
    mut v_sync_7033_: u8,
    mut v_x_7034_: *mut LeanObject,
    mut v_x_7035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    v___x_7037_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(
        v_f_7031_,
        v_prio_7032_,
        v_sync_7033_,
        v_x_7034_,
        v_x_7035_,
    );
    return v___x_7037_;
}
pub unsafe fn l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(
    mut v_00_u03b1_7038_: *mut LeanObject,
    mut v_00_u03b2_7039_: *mut LeanObject,
    mut v_f_7040_: *mut LeanObject,
    mut v_prio_7041_: *mut LeanObject,
    mut v_sync_7042_: *mut LeanObject,
    mut v_x_7043_: *mut LeanObject,
    mut v_x_7044_: *mut LeanObject,
    mut v_a_7045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7046_: u8 = 0;
    let mut v_res_7047_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7046_ = (lean_unbox(v_sync_7042_) as u8);
    v_res_7047_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(
        v_00_u03b1_7038_,
        v_00_u03b2_7039_,
        v_f_7040_,
        v_prio_7041_,
        v_sync_boxed_7046_,
        v_x_7043_,
        v_x_7044_,
    );
    return v_res_7047_;
}
pub unsafe fn l_BaseIO_mapTasks___redArg(
    mut v_f_7048_: *mut LeanObject,
    mut v_tasks_7049_: *mut LeanObject,
    mut v_prio_7050_: *mut LeanObject,
    mut v_sync_7051_: u8,
) -> *mut LeanObject {
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    v___x_7053_ = lean_box(0);
    v___x_7054_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(
        v_f_7048_,
        v_prio_7050_,
        v_sync_7051_,
        v_tasks_7049_,
        v___x_7053_,
    );
    return v___x_7054_;
}
pub unsafe fn l_BaseIO_mapTasks___redArg___boxed(
    mut v_f_7055_: *mut LeanObject,
    mut v_tasks_7056_: *mut LeanObject,
    mut v_prio_7057_: *mut LeanObject,
    mut v_sync_7058_: *mut LeanObject,
    mut v_a_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7060_: u8 = 0;
    let mut v_res_7061_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7060_ = (lean_unbox(v_sync_7058_) as u8);
    v_res_7061_ =
        l_BaseIO_mapTasks___redArg(v_f_7055_, v_tasks_7056_, v_prio_7057_, v_sync_boxed_7060_);
    return v_res_7061_;
}
pub unsafe fn l_BaseIO_mapTasks(
    mut v_00_u03b1_7062_: *mut LeanObject,
    mut v_00_u03b2_7063_: *mut LeanObject,
    mut v_f_7064_: *mut LeanObject,
    mut v_tasks_7065_: *mut LeanObject,
    mut v_prio_7066_: *mut LeanObject,
    mut v_sync_7067_: u8,
) -> *mut LeanObject {
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    v___x_7069_ = l_BaseIO_mapTasks___redArg(v_f_7064_, v_tasks_7065_, v_prio_7066_, v_sync_7067_);
    return v___x_7069_;
}
pub unsafe fn l_BaseIO_mapTasks___boxed(
    mut v_00_u03b1_7070_: *mut LeanObject,
    mut v_00_u03b2_7071_: *mut LeanObject,
    mut v_f_7072_: *mut LeanObject,
    mut v_tasks_7073_: *mut LeanObject,
    mut v_prio_7074_: *mut LeanObject,
    mut v_sync_7075_: *mut LeanObject,
    mut v_a_7076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7077_: u8 = 0;
    let mut v_res_7078_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7077_ = (lean_unbox(v_sync_7075_) as u8);
    v_res_7078_ = l_BaseIO_mapTasks(
        v_00_u03b1_7070_,
        v_00_u03b2_7071_,
        v_f_7072_,
        v_tasks_7073_,
        v_prio_7074_,
        v_sync_boxed_7077_,
    );
    return v_res_7078_;
}
pub unsafe fn l_EIO_asTask___redArg(
    mut v_act_7079_: *mut LeanObject,
    mut v_prio_7080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    v___x_7082_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7082_, 0, lean_box(0));
    lean_closure_set(v___x_7082_, 1, lean_box(0));
    lean_closure_set(v___x_7082_, 2, v_act_7079_);
    v___x_7083_ = lean_io_as_task(v___x_7082_, v_prio_7080_);
    return v___x_7083_;
}
pub unsafe fn l_EIO_asTask___redArg___boxed(
    mut v_act_7084_: *mut LeanObject,
    mut v_prio_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7087_: *mut LeanObject = core::ptr::null_mut();
    v_res_7087_ = l_EIO_asTask___redArg(v_act_7084_, v_prio_7085_);
    return v_res_7087_;
}
pub unsafe fn l_EIO_asTask(
    mut v_00_u03b5_7088_: *mut LeanObject,
    mut v_00_u03b1_7089_: *mut LeanObject,
    mut v_act_7090_: *mut LeanObject,
    mut v_prio_7091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    v___x_7093_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7093_, 0, lean_box(0));
    lean_closure_set(v___x_7093_, 1, lean_box(0));
    lean_closure_set(v___x_7093_, 2, v_act_7090_);
    v___x_7094_ = lean_io_as_task(v___x_7093_, v_prio_7091_);
    return v___x_7094_;
}
pub unsafe fn l_EIO_asTask___boxed(
    mut v_00_u03b5_7095_: *mut LeanObject,
    mut v_00_u03b1_7096_: *mut LeanObject,
    mut v_act_7097_: *mut LeanObject,
    mut v_prio_7098_: *mut LeanObject,
    mut v_a_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7100_: *mut LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_EIO_asTask(
        v_00_u03b5_7095_,
        v_00_u03b1_7096_,
        v_act_7097_,
        v_prio_7098_,
    );
    return v_res_7100_;
}
pub unsafe fn l_EIO_mapTask___redArg___lam__0(
    mut v_f_7101_: *mut LeanObject,
    mut v_a_7102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7108_: u8 = 0;
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7112_: u8 = 0;
    let mut v_a_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7116_: u8 = 0;
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7104_ = lean_apply_2(v_f_7101_, v_a_7102_, lean_box(0));
                if lean_obj_tag(v___x_7104_) == 0 {
                    v_a_7105_ = lean_ctor_get(v___x_7104_, 0);
                    v_isSharedCheck_7112_ = (!lean_is_exclusive(v___x_7104_)) as u8;
                    if v_isSharedCheck_7112_ == 0 {
                        v___x_7107_ = v___x_7104_;
                        v_isShared_7108_ = v_isSharedCheck_7112_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7105_);
                        lean_dec(v___x_7104_);
                        v___x_7107_ = lean_box(0);
                        v_isShared_7108_ = v_isSharedCheck_7112_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7113_ = lean_ctor_get(v___x_7104_, 0);
                    v_isSharedCheck_7120_ = (!lean_is_exclusive(v___x_7104_)) as u8;
                    if v_isSharedCheck_7120_ == 0 {
                        v___x_7115_ = v___x_7104_;
                        v_isShared_7116_ = v_isSharedCheck_7120_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7113_);
                        lean_dec(v___x_7104_);
                        v___x_7115_ = lean_box(0);
                        v_isShared_7116_ = v_isSharedCheck_7120_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7108_ == 0 {
                    lean_ctor_set_tag(v___x_7107_, 1);
                    v___x_7110_ = v___x_7107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7111_, 0, v_a_7105_);
                    v___x_7110_ = v_reuseFailAlloc_7111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7110_;
            }
            3 => {
                if v_isShared_7116_ == 0 {
                    lean_ctor_set_tag(v___x_7115_, 0);
                    v___x_7118_ = v___x_7115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7119_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7119_, 0, v_a_7113_);
                    v___x_7118_ = v_reuseFailAlloc_7119_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_mapTask___redArg___lam__0___boxed(
    mut v_f_7121_: *mut LeanObject,
    mut v_a_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7124_: *mut LeanObject = core::ptr::null_mut();
    v_res_7124_ = l_EIO_mapTask___redArg___lam__0(v_f_7121_, v_a_7122_);
    return v_res_7124_;
}
pub unsafe fn l_EIO_mapTask___redArg(
    mut v_f_7125_: *mut LeanObject,
    mut v_t_7126_: *mut LeanObject,
    mut v_prio_7127_: *mut LeanObject,
    mut v_sync_7128_: u8,
) -> *mut LeanObject {
    let mut v___f_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    v___f_7130_ = lean_alloc_closure(
        l_EIO_mapTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7130_, 0, v_f_7125_);
    v___x_7131_ = lean_io_map_task(v___f_7130_, v_t_7126_, v_prio_7127_, v_sync_7128_);
    return v___x_7131_;
}
pub unsafe fn l_EIO_mapTask___redArg___boxed(
    mut v_f_7132_: *mut LeanObject,
    mut v_t_7133_: *mut LeanObject,
    mut v_prio_7134_: *mut LeanObject,
    mut v_sync_7135_: *mut LeanObject,
    mut v_a_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7137_: u8 = 0;
    let mut v_res_7138_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7137_ = (lean_unbox(v_sync_7135_) as u8);
    v_res_7138_ = l_EIO_mapTask___redArg(v_f_7132_, v_t_7133_, v_prio_7134_, v_sync_boxed_7137_);
    return v_res_7138_;
}
pub unsafe fn l_EIO_mapTask(
    mut v_00_u03b1_7139_: *mut LeanObject,
    mut v_00_u03b5_7140_: *mut LeanObject,
    mut v_00_u03b2_7141_: *mut LeanObject,
    mut v_f_7142_: *mut LeanObject,
    mut v_t_7143_: *mut LeanObject,
    mut v_prio_7144_: *mut LeanObject,
    mut v_sync_7145_: u8,
) -> *mut LeanObject {
    let mut v___f_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    v___f_7147_ = lean_alloc_closure(
        l_EIO_mapTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7147_, 0, v_f_7142_);
    v___x_7148_ = lean_io_map_task(v___f_7147_, v_t_7143_, v_prio_7144_, v_sync_7145_);
    return v___x_7148_;
}
pub unsafe fn l_EIO_mapTask___boxed(
    mut v_00_u03b1_7149_: *mut LeanObject,
    mut v_00_u03b5_7150_: *mut LeanObject,
    mut v_00_u03b2_7151_: *mut LeanObject,
    mut v_f_7152_: *mut LeanObject,
    mut v_t_7153_: *mut LeanObject,
    mut v_prio_7154_: *mut LeanObject,
    mut v_sync_7155_: *mut LeanObject,
    mut v_a_7156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7157_: u8 = 0;
    let mut v_res_7158_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7157_ = (lean_unbox(v_sync_7155_) as u8);
    v_res_7158_ = l_EIO_mapTask(
        v_00_u03b1_7149_,
        v_00_u03b5_7150_,
        v_00_u03b2_7151_,
        v_f_7152_,
        v_t_7153_,
        v_prio_7154_,
        v_sync_boxed_7157_,
    );
    return v_res_7158_;
}
pub unsafe fn l_EIO_bindTask___redArg___lam__0(
    mut v_f_7159_: *mut LeanObject,
    mut v_a_7160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7167_: u8 = 0;
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7162_ = lean_apply_2(v_f_7159_, v_a_7160_, lean_box(0));
                if lean_obj_tag(v___x_7162_) == 0 {
                    v_a_7163_ = lean_ctor_get(v___x_7162_, 0);
                    lean_inc(v_a_7163_);
                    lean_dec_ref_known(v___x_7162_, 1);
                    return v_a_7163_;
                } else {
                    v_a_7164_ = lean_ctor_get(v___x_7162_, 0);
                    v_isSharedCheck_7172_ = (!lean_is_exclusive(v___x_7162_)) as u8;
                    if v_isSharedCheck_7172_ == 0 {
                        v___x_7166_ = v___x_7162_;
                        v_isShared_7167_ = v_isSharedCheck_7172_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7164_);
                        lean_dec(v___x_7162_);
                        v___x_7166_ = lean_box(0);
                        v_isShared_7167_ = v_isSharedCheck_7172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7167_ == 0 {
                    lean_ctor_set_tag(v___x_7166_, 0);
                    v___x_7169_ = v___x_7166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7171_, 0, v_a_7164_);
                    v___x_7169_ = v_reuseFailAlloc_7171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7170_ = lean_task_pure(v___x_7169_);
                return v___x_7170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_bindTask___redArg___lam__0___boxed(
    mut v_f_7173_: *mut LeanObject,
    mut v_a_7174_: *mut LeanObject,
    mut v___y_7175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7176_: *mut LeanObject = core::ptr::null_mut();
    v_res_7176_ = l_EIO_bindTask___redArg___lam__0(v_f_7173_, v_a_7174_);
    return v_res_7176_;
}
pub unsafe fn l_EIO_bindTask___redArg(
    mut v_t_7177_: *mut LeanObject,
    mut v_f_7178_: *mut LeanObject,
    mut v_prio_7179_: *mut LeanObject,
    mut v_sync_7180_: u8,
) -> *mut LeanObject {
    let mut v___f_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    v___f_7182_ = lean_alloc_closure(
        l_EIO_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7182_, 0, v_f_7178_);
    v___x_7183_ = lean_io_bind_task(v_t_7177_, v___f_7182_, v_prio_7179_, v_sync_7180_);
    return v___x_7183_;
}
pub unsafe fn l_EIO_bindTask___redArg___boxed(
    mut v_t_7184_: *mut LeanObject,
    mut v_f_7185_: *mut LeanObject,
    mut v_prio_7186_: *mut LeanObject,
    mut v_sync_7187_: *mut LeanObject,
    mut v_a_7188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7189_: u8 = 0;
    let mut v_res_7190_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7189_ = (lean_unbox(v_sync_7187_) as u8);
    v_res_7190_ = l_EIO_bindTask___redArg(v_t_7184_, v_f_7185_, v_prio_7186_, v_sync_boxed_7189_);
    return v_res_7190_;
}
pub unsafe fn l_EIO_bindTask(
    mut v_00_u03b1_7191_: *mut LeanObject,
    mut v_00_u03b5_7192_: *mut LeanObject,
    mut v_00_u03b2_7193_: *mut LeanObject,
    mut v_t_7194_: *mut LeanObject,
    mut v_f_7195_: *mut LeanObject,
    mut v_prio_7196_: *mut LeanObject,
    mut v_sync_7197_: u8,
) -> *mut LeanObject {
    let mut v___f_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    v___f_7199_ = lean_alloc_closure(
        l_EIO_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7199_, 0, v_f_7195_);
    v___x_7200_ = lean_io_bind_task(v_t_7194_, v___f_7199_, v_prio_7196_, v_sync_7197_);
    return v___x_7200_;
}
pub unsafe fn l_EIO_bindTask___boxed(
    mut v_00_u03b1_7201_: *mut LeanObject,
    mut v_00_u03b5_7202_: *mut LeanObject,
    mut v_00_u03b2_7203_: *mut LeanObject,
    mut v_t_7204_: *mut LeanObject,
    mut v_f_7205_: *mut LeanObject,
    mut v_prio_7206_: *mut LeanObject,
    mut v_sync_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7209_: u8 = 0;
    let mut v_res_7210_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7209_ = (lean_unbox(v_sync_7207_) as u8);
    v_res_7210_ = l_EIO_bindTask(
        v_00_u03b1_7201_,
        v_00_u03b5_7202_,
        v_00_u03b2_7203_,
        v_t_7204_,
        v_f_7205_,
        v_prio_7206_,
        v_sync_boxed_7209_,
    );
    return v_res_7210_;
}
pub unsafe fn l_EIO_chainTask___redArg___lam__0(
    mut v_f_7211_: *mut LeanObject,
    mut v_a_7212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7218_: u8 = 0;
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7222_: u8 = 0;
    let mut v_a_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7226_: u8 = 0;
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7214_ = lean_apply_2(v_f_7211_, v_a_7212_, lean_box(0));
                if lean_obj_tag(v___x_7214_) == 0 {
                    v_a_7215_ = lean_ctor_get(v___x_7214_, 0);
                    v_isSharedCheck_7222_ = (!lean_is_exclusive(v___x_7214_)) as u8;
                    if v_isSharedCheck_7222_ == 0 {
                        v___x_7217_ = v___x_7214_;
                        v_isShared_7218_ = v_isSharedCheck_7222_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7215_);
                        lean_dec(v___x_7214_);
                        v___x_7217_ = lean_box(0);
                        v_isShared_7218_ = v_isSharedCheck_7222_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7223_ = lean_ctor_get(v___x_7214_, 0);
                    v_isSharedCheck_7230_ = (!lean_is_exclusive(v___x_7214_)) as u8;
                    if v_isSharedCheck_7230_ == 0 {
                        v___x_7225_ = v___x_7214_;
                        v_isShared_7226_ = v_isSharedCheck_7230_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7223_);
                        lean_dec(v___x_7214_);
                        v___x_7225_ = lean_box(0);
                        v_isShared_7226_ = v_isSharedCheck_7230_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7218_ == 0 {
                    lean_ctor_set_tag(v___x_7217_, 1);
                    v___x_7220_ = v___x_7217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7221_, 0, v_a_7215_);
                    v___x_7220_ = v_reuseFailAlloc_7221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7220_;
            }
            3 => {
                if v_isShared_7226_ == 0 {
                    lean_ctor_set_tag(v___x_7225_, 0);
                    v___x_7228_ = v___x_7225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7229_, 0, v_a_7223_);
                    v___x_7228_ = v_reuseFailAlloc_7229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_chainTask___redArg___lam__0___boxed(
    mut v_f_7231_: *mut LeanObject,
    mut v_a_7232_: *mut LeanObject,
    mut v___y_7233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7234_: *mut LeanObject = core::ptr::null_mut();
    v_res_7234_ = l_EIO_chainTask___redArg___lam__0(v_f_7231_, v_a_7232_);
    return v_res_7234_;
}
pub unsafe fn l_EIO_chainTask___redArg(
    mut v_t_7235_: *mut LeanObject,
    mut v_f_7236_: *mut LeanObject,
    mut v_prio_7237_: *mut LeanObject,
    mut v_sync_7238_: u8,
) -> *mut LeanObject {
    let mut v___f_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    v___f_7240_ = lean_alloc_closure(
        l_EIO_chainTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7240_, 0, v_f_7236_);
    v___x_7241_ = lean_io_map_task(v___f_7240_, v_t_7235_, v_prio_7237_, v_sync_7238_);
    lean_dec_ref(v___x_7241_);
    v___x_7242_ = lean_box(0);
    v___x_7243_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7243_, 0, v___x_7242_);
    return v___x_7243_;
}
pub unsafe fn l_EIO_chainTask___redArg___boxed(
    mut v_t_7244_: *mut LeanObject,
    mut v_f_7245_: *mut LeanObject,
    mut v_prio_7246_: *mut LeanObject,
    mut v_sync_7247_: *mut LeanObject,
    mut v_a_7248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7249_: u8 = 0;
    let mut v_res_7250_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7249_ = (lean_unbox(v_sync_7247_) as u8);
    v_res_7250_ = l_EIO_chainTask___redArg(v_t_7244_, v_f_7245_, v_prio_7246_, v_sync_boxed_7249_);
    return v_res_7250_;
}
pub unsafe fn l_EIO_chainTask(
    mut v_00_u03b1_7251_: *mut LeanObject,
    mut v_00_u03b5_7252_: *mut LeanObject,
    mut v_t_7253_: *mut LeanObject,
    mut v_f_7254_: *mut LeanObject,
    mut v_prio_7255_: *mut LeanObject,
    mut v_sync_7256_: u8,
) -> *mut LeanObject {
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    v___x_7258_ = l_EIO_chainTask___redArg(v_t_7253_, v_f_7254_, v_prio_7255_, v_sync_7256_);
    return v___x_7258_;
}
pub unsafe fn l_EIO_chainTask___boxed(
    mut v_00_u03b1_7259_: *mut LeanObject,
    mut v_00_u03b5_7260_: *mut LeanObject,
    mut v_t_7261_: *mut LeanObject,
    mut v_f_7262_: *mut LeanObject,
    mut v_prio_7263_: *mut LeanObject,
    mut v_sync_7264_: *mut LeanObject,
    mut v_a_7265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7266_: u8 = 0;
    let mut v_res_7267_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7266_ = (lean_unbox(v_sync_7264_) as u8);
    v_res_7267_ = l_EIO_chainTask(
        v_00_u03b1_7259_,
        v_00_u03b5_7260_,
        v_t_7261_,
        v_f_7262_,
        v_prio_7263_,
        v_sync_boxed_7266_,
    );
    return v_res_7267_;
}
pub unsafe fn l_EIO_mapTasks___redArg___lam__0(
    mut v_f_7268_: *mut LeanObject,
    mut v_as_7269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7275_: u8 = 0;
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7279_: u8 = 0;
    let mut v_a_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7283_: u8 = 0;
    let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7271_ = lean_apply_2(v_f_7268_, v_as_7269_, lean_box(0));
                if lean_obj_tag(v___x_7271_) == 0 {
                    v_a_7272_ = lean_ctor_get(v___x_7271_, 0);
                    v_isSharedCheck_7279_ = (!lean_is_exclusive(v___x_7271_)) as u8;
                    if v_isSharedCheck_7279_ == 0 {
                        v___x_7274_ = v___x_7271_;
                        v_isShared_7275_ = v_isSharedCheck_7279_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7272_);
                        lean_dec(v___x_7271_);
                        v___x_7274_ = lean_box(0);
                        v_isShared_7275_ = v_isSharedCheck_7279_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7280_ = lean_ctor_get(v___x_7271_, 0);
                    v_isSharedCheck_7287_ = (!lean_is_exclusive(v___x_7271_)) as u8;
                    if v_isSharedCheck_7287_ == 0 {
                        v___x_7282_ = v___x_7271_;
                        v_isShared_7283_ = v_isSharedCheck_7287_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7280_);
                        lean_dec(v___x_7271_);
                        v___x_7282_ = lean_box(0);
                        v_isShared_7283_ = v_isSharedCheck_7287_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7275_ == 0 {
                    lean_ctor_set_tag(v___x_7274_, 1);
                    v___x_7277_ = v___x_7274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7278_, 0, v_a_7272_);
                    v___x_7277_ = v_reuseFailAlloc_7278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7277_;
            }
            3 => {
                if v_isShared_7283_ == 0 {
                    lean_ctor_set_tag(v___x_7282_, 0);
                    v___x_7285_ = v___x_7282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7286_, 0, v_a_7280_);
                    v___x_7285_ = v_reuseFailAlloc_7286_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EIO_mapTasks___redArg___lam__0___boxed(
    mut v_f_7288_: *mut LeanObject,
    mut v_as_7289_: *mut LeanObject,
    mut v___y_7290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7291_: *mut LeanObject = core::ptr::null_mut();
    v_res_7291_ = l_EIO_mapTasks___redArg___lam__0(v_f_7288_, v_as_7289_);
    return v_res_7291_;
}
pub unsafe fn l_EIO_mapTasks___redArg(
    mut v_f_7292_: *mut LeanObject,
    mut v_tasks_7293_: *mut LeanObject,
    mut v_prio_7294_: *mut LeanObject,
    mut v_sync_7295_: u8,
) -> *mut LeanObject {
    let mut v___f_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    v___f_7297_ = lean_alloc_closure(
        l_EIO_mapTasks___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7297_, 0, v_f_7292_);
    v___x_7298_ =
        l_BaseIO_mapTasks___redArg(v___f_7297_, v_tasks_7293_, v_prio_7294_, v_sync_7295_);
    return v___x_7298_;
}
pub unsafe fn l_EIO_mapTasks___redArg___boxed(
    mut v_f_7299_: *mut LeanObject,
    mut v_tasks_7300_: *mut LeanObject,
    mut v_prio_7301_: *mut LeanObject,
    mut v_sync_7302_: *mut LeanObject,
    mut v_a_7303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7304_: u8 = 0;
    let mut v_res_7305_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7304_ = (lean_unbox(v_sync_7302_) as u8);
    v_res_7305_ =
        l_EIO_mapTasks___redArg(v_f_7299_, v_tasks_7300_, v_prio_7301_, v_sync_boxed_7304_);
    return v_res_7305_;
}
pub unsafe fn l_EIO_mapTasks(
    mut v_00_u03b1_7306_: *mut LeanObject,
    mut v_00_u03b5_7307_: *mut LeanObject,
    mut v_00_u03b2_7308_: *mut LeanObject,
    mut v_f_7309_: *mut LeanObject,
    mut v_tasks_7310_: *mut LeanObject,
    mut v_prio_7311_: *mut LeanObject,
    mut v_sync_7312_: u8,
) -> *mut LeanObject {
    let mut v___f_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    v___f_7314_ = lean_alloc_closure(
        l_EIO_mapTasks___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7314_, 0, v_f_7309_);
    v___x_7315_ =
        l_BaseIO_mapTasks___redArg(v___f_7314_, v_tasks_7310_, v_prio_7311_, v_sync_7312_);
    return v___x_7315_;
}
pub unsafe fn l_EIO_mapTasks___boxed(
    mut v_00_u03b1_7316_: *mut LeanObject,
    mut v_00_u03b5_7317_: *mut LeanObject,
    mut v_00_u03b2_7318_: *mut LeanObject,
    mut v_f_7319_: *mut LeanObject,
    mut v_tasks_7320_: *mut LeanObject,
    mut v_prio_7321_: *mut LeanObject,
    mut v_sync_7322_: *mut LeanObject,
    mut v_a_7323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7324_: u8 = 0;
    let mut v_res_7325_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7324_ = (lean_unbox(v_sync_7322_) as u8);
    v_res_7325_ = l_EIO_mapTasks(
        v_00_u03b1_7316_,
        v_00_u03b5_7317_,
        v_00_u03b2_7318_,
        v_f_7319_,
        v_tasks_7320_,
        v_prio_7321_,
        v_sync_boxed_7324_,
    );
    return v_res_7325_;
}
pub unsafe fn l_IO_ofExcept___redArg(
    mut v_inst_7326_: *mut LeanObject,
    mut v_e_7327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7332_: u8 = 0;
    let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7338_: u8 = 0;
    let mut v_a_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7342_: u8 = 0;
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_7327_) == 0 {
                    v_a_7329_ = lean_ctor_get(v_e_7327_, 0);
                    v_isSharedCheck_7338_ = (!lean_is_exclusive(v_e_7327_)) as u8;
                    if v_isSharedCheck_7338_ == 0 {
                        v___x_7331_ = v_e_7327_;
                        v_isShared_7332_ = v_isSharedCheck_7338_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7329_);
                        lean_dec(v_e_7327_);
                        v___x_7331_ = lean_box(0);
                        v_isShared_7332_ = v_isSharedCheck_7338_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_7326_);
                    v_a_7339_ = lean_ctor_get(v_e_7327_, 0);
                    v_isSharedCheck_7346_ = (!lean_is_exclusive(v_e_7327_)) as u8;
                    if v_isSharedCheck_7346_ == 0 {
                        v___x_7341_ = v_e_7327_;
                        v_isShared_7342_ = v_isSharedCheck_7346_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7339_);
                        lean_dec(v_e_7327_);
                        v___x_7341_ = lean_box(0);
                        v_isShared_7342_ = v_isSharedCheck_7346_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7333_ = lean_apply_1(v_inst_7326_, v_a_7329_);
                v___x_7334_ = lean_mk_io_user_error(v___x_7333_);
                if v_isShared_7332_ == 0 {
                    lean_ctor_set_tag(v___x_7331_, 1);
                    lean_ctor_set(v___x_7331_, 0, v___x_7334_);
                    v___x_7336_ = v___x_7331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7337_, 0, v___x_7334_);
                    v___x_7336_ = v_reuseFailAlloc_7337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7336_;
            }
            3 => {
                if v_isShared_7342_ == 0 {
                    lean_ctor_set_tag(v___x_7341_, 0);
                    v___x_7344_ = v___x_7341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7345_, 0, v_a_7339_);
                    v___x_7344_ = v_reuseFailAlloc_7345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___redArg___boxed(
    mut v_inst_7347_: *mut LeanObject,
    mut v_e_7348_: *mut LeanObject,
    mut v_a_7349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7350_: *mut LeanObject = core::ptr::null_mut();
    v_res_7350_ = l_IO_ofExcept___redArg(v_inst_7347_, v_e_7348_);
    return v_res_7350_;
}
pub unsafe fn l_IO_ofExcept(
    mut v_00_u03b5_7351_: *mut LeanObject,
    mut v_00_u03b1_7352_: *mut LeanObject,
    mut v_inst_7353_: *mut LeanObject,
    mut v_e_7354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    v___x_7356_ = l_IO_ofExcept___redArg(v_inst_7353_, v_e_7354_);
    return v___x_7356_;
}
pub unsafe fn l_IO_ofExcept___boxed(
    mut v_00_u03b5_7357_: *mut LeanObject,
    mut v_00_u03b1_7358_: *mut LeanObject,
    mut v_inst_7359_: *mut LeanObject,
    mut v_e_7360_: *mut LeanObject,
    mut v_a_7361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7362_: *mut LeanObject = core::ptr::null_mut();
    v_res_7362_ = l_IO_ofExcept(v_00_u03b5_7357_, v_00_u03b1_7358_, v_inst_7359_, v_e_7360_);
    return v_res_7362_;
}
pub unsafe fn l_IO_lazyPure___redArg(mut v_fn_7363_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    v___x_7365_ = lean_box(0);
    v___x_7366_ = lean_apply_1(v_fn_7363_, v___x_7365_);
    v___x_7367_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7367_, 0, v___x_7366_);
    return v___x_7367_;
}
pub unsafe fn l_IO_lazyPure___redArg___boxed(
    mut v_fn_7368_: *mut LeanObject,
    mut v_a_7369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7370_: *mut LeanObject = core::ptr::null_mut();
    v_res_7370_ = l_IO_lazyPure___redArg(v_fn_7368_);
    return v_res_7370_;
}
pub unsafe fn l_IO_lazyPure(
    mut v_00_u03b1_7371_: *mut LeanObject,
    mut v_fn_7372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    v___x_7374_ = l_IO_lazyPure___redArg(v_fn_7372_);
    return v___x_7374_;
}
pub unsafe fn l_IO_lazyPure___boxed(
    mut v_00_u03b1_7375_: *mut LeanObject,
    mut v_fn_7376_: *mut LeanObject,
    mut v_a_7377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7378_: *mut LeanObject = core::ptr::null_mut();
    v_res_7378_ = l_IO_lazyPure(v_00_u03b1_7375_, v_fn_7376_);
    return v_res_7378_;
}
pub unsafe fn l_IO_monoMsNow___boxed(
    mut v_a_00___x40___internal___hyg_7380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7381_: *mut LeanObject = core::ptr::null_mut();
    v_res_7381_ = lean_io_mono_ms_now();
    return v_res_7381_;
}
pub unsafe fn l_IO_monoNanosNow___boxed(
    mut v_a_00___x40___internal___hyg_7383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7384_: *mut LeanObject = core::ptr::null_mut();
    v_res_7384_ = lean_io_mono_nanos_now();
    return v_res_7384_;
}
pub unsafe fn l_IO_getRandomBytes___boxed(
    mut v_nBytes_7387_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nBytes_boxed_7389_: usize = 0;
    let mut v_res_7390_: *mut LeanObject = core::ptr::null_mut();
    v_nBytes_boxed_7389_ = lean_unbox_usize(v_nBytes_7387_);
    lean_dec(v_nBytes_7387_);
    v_res_7390_ = lean_io_get_random_bytes(v_nBytes_boxed_7389_);
    return v_res_7390_;
}
pub unsafe fn l_IO_sleep___lam__0(mut v_x_7392_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
    v___x_7393_ = lean_box(0);
    return v___x_7393_;
}
pub unsafe fn l_IO_sleep___lam__0___boxed(
    mut v_s_7394_: *mut LeanObject,
    mut v_x_7395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7396_: *mut LeanObject = core::ptr::null_mut();
    v_res_7396_ = l_IO_sleep___lam__0(v_x_7395_);
    return v_res_7396_;
}
pub unsafe fn l_IO_sleep(mut v_ms_7397_: u32) -> *mut LeanObject {
    let mut v___f_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    v___f_7399_ = lean_alloc_closure(l_IO_sleep___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_7399_, 0, lean_box(0));
    v___x_7400_ = lean_dbg_sleep(v_ms_7397_, v___f_7399_);
    return v___x_7400_;
}
pub unsafe fn l_IO_sleep___boxed(
    mut v_ms_7401_: *mut LeanObject,
    mut v_s_7402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ms_boxed_7403_: u32 = 0;
    let mut v_res_7404_: *mut LeanObject = core::ptr::null_mut();
    v_ms_boxed_7403_ = lean_unbox_uint32(v_ms_7401_);
    lean_dec(v_ms_7401_);
    v_res_7404_ = l_IO_sleep(v_ms_boxed_7403_);
    return v_res_7404_;
}
pub unsafe fn l_IO_asTask___redArg(
    mut v_act_7405_: *mut LeanObject,
    mut v_prio_7406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    v___x_7408_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7408_, 0, lean_box(0));
    lean_closure_set(v___x_7408_, 1, lean_box(0));
    lean_closure_set(v___x_7408_, 2, v_act_7405_);
    v___x_7409_ = lean_io_as_task(v___x_7408_, v_prio_7406_);
    return v___x_7409_;
}
pub unsafe fn l_IO_asTask___redArg___boxed(
    mut v_act_7410_: *mut LeanObject,
    mut v_prio_7411_: *mut LeanObject,
    mut v_a_7412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7413_: *mut LeanObject = core::ptr::null_mut();
    v_res_7413_ = l_IO_asTask___redArg(v_act_7410_, v_prio_7411_);
    return v_res_7413_;
}
pub unsafe fn l_IO_asTask(
    mut v_00_u03b1_7414_: *mut LeanObject,
    mut v_act_7415_: *mut LeanObject,
    mut v_prio_7416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    v___x_7418_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7418_, 0, lean_box(0));
    lean_closure_set(v___x_7418_, 1, lean_box(0));
    lean_closure_set(v___x_7418_, 2, v_act_7415_);
    v___x_7419_ = lean_io_as_task(v___x_7418_, v_prio_7416_);
    return v___x_7419_;
}
pub unsafe fn l_IO_asTask___boxed(
    mut v_00_u03b1_7420_: *mut LeanObject,
    mut v_act_7421_: *mut LeanObject,
    mut v_prio_7422_: *mut LeanObject,
    mut v_a_7423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7424_: *mut LeanObject = core::ptr::null_mut();
    v_res_7424_ = l_IO_asTask(v_00_u03b1_7420_, v_act_7421_, v_prio_7422_);
    return v_res_7424_;
}
pub unsafe fn l_IO_mapTask___redArg___lam__0(
    mut v_f_7425_: *mut LeanObject,
    mut v_a_7426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7432_: u8 = 0;
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7436_: u8 = 0;
    let mut v_a_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7440_: u8 = 0;
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7428_ = lean_apply_2(v_f_7425_, v_a_7426_, lean_box(0));
                if lean_obj_tag(v___x_7428_) == 0 {
                    v_a_7429_ = lean_ctor_get(v___x_7428_, 0);
                    v_isSharedCheck_7436_ = (!lean_is_exclusive(v___x_7428_)) as u8;
                    if v_isSharedCheck_7436_ == 0 {
                        v___x_7431_ = v___x_7428_;
                        v_isShared_7432_ = v_isSharedCheck_7436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7429_);
                        lean_dec(v___x_7428_);
                        v___x_7431_ = lean_box(0);
                        v_isShared_7432_ = v_isSharedCheck_7436_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7437_ = lean_ctor_get(v___x_7428_, 0);
                    v_isSharedCheck_7444_ = (!lean_is_exclusive(v___x_7428_)) as u8;
                    if v_isSharedCheck_7444_ == 0 {
                        v___x_7439_ = v___x_7428_;
                        v_isShared_7440_ = v_isSharedCheck_7444_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7437_);
                        lean_dec(v___x_7428_);
                        v___x_7439_ = lean_box(0);
                        v_isShared_7440_ = v_isSharedCheck_7444_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7432_ == 0 {
                    lean_ctor_set_tag(v___x_7431_, 1);
                    v___x_7434_ = v___x_7431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7435_, 0, v_a_7429_);
                    v___x_7434_ = v_reuseFailAlloc_7435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7434_;
            }
            3 => {
                if v_isShared_7440_ == 0 {
                    lean_ctor_set_tag(v___x_7439_, 0);
                    v___x_7442_ = v___x_7439_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7443_, 0, v_a_7437_);
                    v___x_7442_ = v_reuseFailAlloc_7443_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_mapTask___redArg___lam__0___boxed(
    mut v_f_7445_: *mut LeanObject,
    mut v_a_7446_: *mut LeanObject,
    mut v___y_7447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7448_: *mut LeanObject = core::ptr::null_mut();
    v_res_7448_ = l_IO_mapTask___redArg___lam__0(v_f_7445_, v_a_7446_);
    return v_res_7448_;
}
pub unsafe fn l_IO_mapTask___redArg(
    mut v_f_7449_: *mut LeanObject,
    mut v_t_7450_: *mut LeanObject,
    mut v_prio_7451_: *mut LeanObject,
    mut v_sync_7452_: u8,
) -> *mut LeanObject {
    let mut v___f_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7455_: *mut LeanObject = core::ptr::null_mut();
    v___f_7454_ = lean_alloc_closure(
        l_IO_mapTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7454_, 0, v_f_7449_);
    v___x_7455_ = lean_io_map_task(v___f_7454_, v_t_7450_, v_prio_7451_, v_sync_7452_);
    return v___x_7455_;
}
pub unsafe fn l_IO_mapTask___redArg___boxed(
    mut v_f_7456_: *mut LeanObject,
    mut v_t_7457_: *mut LeanObject,
    mut v_prio_7458_: *mut LeanObject,
    mut v_sync_7459_: *mut LeanObject,
    mut v_a_7460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7461_: u8 = 0;
    let mut v_res_7462_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7461_ = (lean_unbox(v_sync_7459_) as u8);
    v_res_7462_ = l_IO_mapTask___redArg(v_f_7456_, v_t_7457_, v_prio_7458_, v_sync_boxed_7461_);
    return v_res_7462_;
}
pub unsafe fn l_IO_mapTask(
    mut v_00_u03b1_7463_: *mut LeanObject,
    mut v_00_u03b2_7464_: *mut LeanObject,
    mut v_f_7465_: *mut LeanObject,
    mut v_t_7466_: *mut LeanObject,
    mut v_prio_7467_: *mut LeanObject,
    mut v_sync_7468_: u8,
) -> *mut LeanObject {
    let mut v___f_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
    v___f_7470_ = lean_alloc_closure(
        l_IO_mapTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7470_, 0, v_f_7465_);
    v___x_7471_ = lean_io_map_task(v___f_7470_, v_t_7466_, v_prio_7467_, v_sync_7468_);
    return v___x_7471_;
}
pub unsafe fn l_IO_mapTask___boxed(
    mut v_00_u03b1_7472_: *mut LeanObject,
    mut v_00_u03b2_7473_: *mut LeanObject,
    mut v_f_7474_: *mut LeanObject,
    mut v_t_7475_: *mut LeanObject,
    mut v_prio_7476_: *mut LeanObject,
    mut v_sync_7477_: *mut LeanObject,
    mut v_a_7478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7479_: u8 = 0;
    let mut v_res_7480_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7479_ = (lean_unbox(v_sync_7477_) as u8);
    v_res_7480_ = l_IO_mapTask(
        v_00_u03b1_7472_,
        v_00_u03b2_7473_,
        v_f_7474_,
        v_t_7475_,
        v_prio_7476_,
        v_sync_boxed_7479_,
    );
    return v_res_7480_;
}
pub unsafe fn l_IO_bindTask___redArg___lam__0(
    mut v_f_7481_: *mut LeanObject,
    mut v_a_7482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7489_: u8 = 0;
    let mut v___x_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7484_ = lean_apply_2(v_f_7481_, v_a_7482_, lean_box(0));
                if lean_obj_tag(v___x_7484_) == 0 {
                    v_a_7485_ = lean_ctor_get(v___x_7484_, 0);
                    lean_inc(v_a_7485_);
                    lean_dec_ref_known(v___x_7484_, 1);
                    return v_a_7485_;
                } else {
                    v_a_7486_ = lean_ctor_get(v___x_7484_, 0);
                    v_isSharedCheck_7494_ = (!lean_is_exclusive(v___x_7484_)) as u8;
                    if v_isSharedCheck_7494_ == 0 {
                        v___x_7488_ = v___x_7484_;
                        v_isShared_7489_ = v_isSharedCheck_7494_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7486_);
                        lean_dec(v___x_7484_);
                        v___x_7488_ = lean_box(0);
                        v_isShared_7489_ = v_isSharedCheck_7494_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7489_ == 0 {
                    lean_ctor_set_tag(v___x_7488_, 0);
                    v___x_7491_ = v___x_7488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7493_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7493_, 0, v_a_7486_);
                    v___x_7491_ = v_reuseFailAlloc_7493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7492_ = lean_task_pure(v___x_7491_);
                return v___x_7492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_bindTask___redArg___lam__0___boxed(
    mut v_f_7495_: *mut LeanObject,
    mut v_a_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7498_: *mut LeanObject = core::ptr::null_mut();
    v_res_7498_ = l_IO_bindTask___redArg___lam__0(v_f_7495_, v_a_7496_);
    return v_res_7498_;
}
pub unsafe fn l_IO_bindTask___redArg(
    mut v_t_7499_: *mut LeanObject,
    mut v_f_7500_: *mut LeanObject,
    mut v_prio_7501_: *mut LeanObject,
    mut v_sync_7502_: u8,
) -> *mut LeanObject {
    let mut v___f_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    v___f_7504_ = lean_alloc_closure(
        l_IO_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7504_, 0, v_f_7500_);
    v___x_7505_ = lean_io_bind_task(v_t_7499_, v___f_7504_, v_prio_7501_, v_sync_7502_);
    return v___x_7505_;
}
pub unsafe fn l_IO_bindTask___redArg___boxed(
    mut v_t_7506_: *mut LeanObject,
    mut v_f_7507_: *mut LeanObject,
    mut v_prio_7508_: *mut LeanObject,
    mut v_sync_7509_: *mut LeanObject,
    mut v_a_7510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7511_: u8 = 0;
    let mut v_res_7512_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7511_ = (lean_unbox(v_sync_7509_) as u8);
    v_res_7512_ = l_IO_bindTask___redArg(v_t_7506_, v_f_7507_, v_prio_7508_, v_sync_boxed_7511_);
    return v_res_7512_;
}
pub unsafe fn l_IO_bindTask(
    mut v_00_u03b1_7513_: *mut LeanObject,
    mut v_00_u03b2_7514_: *mut LeanObject,
    mut v_t_7515_: *mut LeanObject,
    mut v_f_7516_: *mut LeanObject,
    mut v_prio_7517_: *mut LeanObject,
    mut v_sync_7518_: u8,
) -> *mut LeanObject {
    let mut v___f_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    v___f_7520_ = lean_alloc_closure(
        l_IO_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7520_, 0, v_f_7516_);
    v___x_7521_ = lean_io_bind_task(v_t_7515_, v___f_7520_, v_prio_7517_, v_sync_7518_);
    return v___x_7521_;
}
pub unsafe fn l_IO_bindTask___boxed(
    mut v_00_u03b1_7522_: *mut LeanObject,
    mut v_00_u03b2_7523_: *mut LeanObject,
    mut v_t_7524_: *mut LeanObject,
    mut v_f_7525_: *mut LeanObject,
    mut v_prio_7526_: *mut LeanObject,
    mut v_sync_7527_: *mut LeanObject,
    mut v_a_7528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7529_: u8 = 0;
    let mut v_res_7530_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7529_ = (lean_unbox(v_sync_7527_) as u8);
    v_res_7530_ = l_IO_bindTask(
        v_00_u03b1_7522_,
        v_00_u03b2_7523_,
        v_t_7524_,
        v_f_7525_,
        v_prio_7526_,
        v_sync_boxed_7529_,
    );
    return v_res_7530_;
}
pub unsafe fn l_IO_chainTask___redArg(
    mut v_t_7531_: *mut LeanObject,
    mut v_f_7532_: *mut LeanObject,
    mut v_prio_7533_: *mut LeanObject,
    mut v_sync_7534_: u8,
) -> *mut LeanObject {
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    v___x_7536_ = l_EIO_chainTask___redArg(v_t_7531_, v_f_7532_, v_prio_7533_, v_sync_7534_);
    return v___x_7536_;
}
pub unsafe fn l_IO_chainTask___redArg___boxed(
    mut v_t_7537_: *mut LeanObject,
    mut v_f_7538_: *mut LeanObject,
    mut v_prio_7539_: *mut LeanObject,
    mut v_sync_7540_: *mut LeanObject,
    mut v_a_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7542_: u8 = 0;
    let mut v_res_7543_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7542_ = (lean_unbox(v_sync_7540_) as u8);
    v_res_7543_ = l_IO_chainTask___redArg(v_t_7537_, v_f_7538_, v_prio_7539_, v_sync_boxed_7542_);
    return v_res_7543_;
}
pub unsafe fn l_IO_chainTask(
    mut v_00_u03b1_7544_: *mut LeanObject,
    mut v_t_7545_: *mut LeanObject,
    mut v_f_7546_: *mut LeanObject,
    mut v_prio_7547_: *mut LeanObject,
    mut v_sync_7548_: u8,
) -> *mut LeanObject {
    let mut v___x_7550_: *mut LeanObject = core::ptr::null_mut();
    v___x_7550_ = l_EIO_chainTask___redArg(v_t_7545_, v_f_7546_, v_prio_7547_, v_sync_7548_);
    return v___x_7550_;
}
pub unsafe fn l_IO_chainTask___boxed(
    mut v_00_u03b1_7551_: *mut LeanObject,
    mut v_t_7552_: *mut LeanObject,
    mut v_f_7553_: *mut LeanObject,
    mut v_prio_7554_: *mut LeanObject,
    mut v_sync_7555_: *mut LeanObject,
    mut v_a_7556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7557_: u8 = 0;
    let mut v_res_7558_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7557_ = (lean_unbox(v_sync_7555_) as u8);
    v_res_7558_ = l_IO_chainTask(
        v_00_u03b1_7551_,
        v_t_7552_,
        v_f_7553_,
        v_prio_7554_,
        v_sync_boxed_7557_,
    );
    return v_res_7558_;
}
pub unsafe fn l_IO_mapTasks___redArg___lam__0(
    mut v_f_7559_: *mut LeanObject,
    mut v_as_7560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7566_: u8 = 0;
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7570_: u8 = 0;
    let mut v_a_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7574_: u8 = 0;
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7562_ = lean_apply_2(v_f_7559_, v_as_7560_, lean_box(0));
                if lean_obj_tag(v___x_7562_) == 0 {
                    v_a_7563_ = lean_ctor_get(v___x_7562_, 0);
                    v_isSharedCheck_7570_ = (!lean_is_exclusive(v___x_7562_)) as u8;
                    if v_isSharedCheck_7570_ == 0 {
                        v___x_7565_ = v___x_7562_;
                        v_isShared_7566_ = v_isSharedCheck_7570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7563_);
                        lean_dec(v___x_7562_);
                        v___x_7565_ = lean_box(0);
                        v_isShared_7566_ = v_isSharedCheck_7570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7571_ = lean_ctor_get(v___x_7562_, 0);
                    v_isSharedCheck_7578_ = (!lean_is_exclusive(v___x_7562_)) as u8;
                    if v_isSharedCheck_7578_ == 0 {
                        v___x_7573_ = v___x_7562_;
                        v_isShared_7574_ = v_isSharedCheck_7578_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7571_);
                        lean_dec(v___x_7562_);
                        v___x_7573_ = lean_box(0);
                        v_isShared_7574_ = v_isSharedCheck_7578_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7566_ == 0 {
                    lean_ctor_set_tag(v___x_7565_, 1);
                    v___x_7568_ = v___x_7565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 0, v_a_7563_);
                    v___x_7568_ = v_reuseFailAlloc_7569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7568_;
            }
            3 => {
                if v_isShared_7574_ == 0 {
                    lean_ctor_set_tag(v___x_7573_, 0);
                    v___x_7576_ = v___x_7573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7577_, 0, v_a_7571_);
                    v___x_7576_ = v_reuseFailAlloc_7577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_mapTasks___redArg___lam__0___boxed(
    mut v_f_7579_: *mut LeanObject,
    mut v_as_7580_: *mut LeanObject,
    mut v___y_7581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7582_: *mut LeanObject = core::ptr::null_mut();
    v_res_7582_ = l_IO_mapTasks___redArg___lam__0(v_f_7579_, v_as_7580_);
    return v_res_7582_;
}
pub unsafe fn l_IO_mapTasks___redArg(
    mut v_f_7583_: *mut LeanObject,
    mut v_tasks_7584_: *mut LeanObject,
    mut v_prio_7585_: *mut LeanObject,
    mut v_sync_7586_: u8,
) -> *mut LeanObject {
    let mut v___f_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    v___f_7588_ = lean_alloc_closure(
        l_IO_mapTasks___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7588_, 0, v_f_7583_);
    v___x_7589_ =
        l_BaseIO_mapTasks___redArg(v___f_7588_, v_tasks_7584_, v_prio_7585_, v_sync_7586_);
    return v___x_7589_;
}
pub unsafe fn l_IO_mapTasks___redArg___boxed(
    mut v_f_7590_: *mut LeanObject,
    mut v_tasks_7591_: *mut LeanObject,
    mut v_prio_7592_: *mut LeanObject,
    mut v_sync_7593_: *mut LeanObject,
    mut v_a_7594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7595_: u8 = 0;
    let mut v_res_7596_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7595_ = (lean_unbox(v_sync_7593_) as u8);
    v_res_7596_ =
        l_IO_mapTasks___redArg(v_f_7590_, v_tasks_7591_, v_prio_7592_, v_sync_boxed_7595_);
    return v_res_7596_;
}
pub unsafe fn l_IO_mapTasks(
    mut v_00_u03b1_7597_: *mut LeanObject,
    mut v_00_u03b2_7598_: *mut LeanObject,
    mut v_f_7599_: *mut LeanObject,
    mut v_tasks_7600_: *mut LeanObject,
    mut v_prio_7601_: *mut LeanObject,
    mut v_sync_7602_: u8,
) -> *mut LeanObject {
    let mut v___f_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: *mut LeanObject = core::ptr::null_mut();
    v___f_7604_ = lean_alloc_closure(
        l_IO_mapTasks___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7604_, 0, v_f_7599_);
    v___x_7605_ =
        l_BaseIO_mapTasks___redArg(v___f_7604_, v_tasks_7600_, v_prio_7601_, v_sync_7602_);
    return v___x_7605_;
}
pub unsafe fn l_IO_mapTasks___boxed(
    mut v_00_u03b1_7606_: *mut LeanObject,
    mut v_00_u03b2_7607_: *mut LeanObject,
    mut v_f_7608_: *mut LeanObject,
    mut v_tasks_7609_: *mut LeanObject,
    mut v_prio_7610_: *mut LeanObject,
    mut v_sync_7611_: *mut LeanObject,
    mut v_a_7612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7613_: u8 = 0;
    let mut v_res_7614_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7613_ = (lean_unbox(v_sync_7611_) as u8);
    v_res_7614_ = l_IO_mapTasks(
        v_00_u03b1_7606_,
        v_00_u03b2_7607_,
        v_f_7608_,
        v_tasks_7609_,
        v_prio_7610_,
        v_sync_boxed_7613_,
    );
    return v_res_7614_;
}
pub unsafe fn l_IO_checkCanceled___boxed(
    mut v_a_00___x40___internal___hyg_7616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7617_: u8 = 0;
    let mut v_r_7618_: *mut LeanObject = core::ptr::null_mut();
    v_res_7617_ = lean_io_check_canceled();
    v_r_7618_ = lean_box((v_res_7617_) as usize);
    return v_r_7618_;
}
pub unsafe fn l_IO_cancel___boxed(
    mut v_00_u03b1_7622_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7623_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7625_: *mut LeanObject = core::ptr::null_mut();
    v_res_7625_ = lean_io_cancel(v_a_00___x40___internal___hyg_7623_);
    lean_dec_ref(v_a_00___x40___internal___hyg_7623_);
    return v_res_7625_;
}
pub unsafe fn l_IO_TaskState_ctorIdx(mut v_x_7626_: u8) -> *mut LeanObject {
    match v_x_7626_ {
        0 => {
            let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
            v___x_7627_ = lean_unsigned_to_nat(0);
            return v___x_7627_;
        }
        1 => {
            let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
            v___x_7628_ = lean_unsigned_to_nat(1);
            return v___x_7628_;
        }
        _ => {
            let mut v___x_7629_: *mut LeanObject = core::ptr::null_mut();
            v___x_7629_ = lean_unsigned_to_nat(2);
            return v___x_7629_;
        }
    }
}
pub unsafe fn l_IO_TaskState_ctorIdx___boxed(mut v_x_7630_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_7631_: u8 = 0;
    let mut v_res_7632_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_7631_ = (lean_unbox(v_x_7630_) as u8);
    v_res_7632_ = l_IO_TaskState_ctorIdx(v_x_boxed_7631_);
    return v_res_7632_;
}
pub unsafe fn l_IO_TaskState_toCtorIdx(mut v_x_7633_: u8) -> *mut LeanObject {
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    v___x_7634_ = l_IO_TaskState_ctorIdx(v_x_7633_);
    return v___x_7634_;
}
pub unsafe fn l_IO_TaskState_toCtorIdx___boxed(mut v_x_7635_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_7636_: u8 = 0;
    let mut v_res_7637_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_7636_ = (lean_unbox(v_x_7635_) as u8);
    v_res_7637_ = l_IO_TaskState_toCtorIdx(v_x_4__boxed_7636_);
    return v_res_7637_;
}
pub unsafe fn l_IO_TaskState_ctorElim___redArg(mut v_k_7638_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_7638_);
    return v_k_7638_;
}
pub unsafe fn l_IO_TaskState_ctorElim___redArg___boxed(
    mut v_k_7639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7640_: *mut LeanObject = core::ptr::null_mut();
    v_res_7640_ = l_IO_TaskState_ctorElim___redArg(v_k_7639_);
    lean_dec(v_k_7639_);
    return v_res_7640_;
}
pub unsafe fn l_IO_TaskState_ctorElim(
    mut v_motive_7641_: *mut LeanObject,
    mut v_ctorIdx_7642_: *mut LeanObject,
    mut v_t_7643_: u8,
    mut v_h_7644_: *mut LeanObject,
    mut v_k_7645_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_7645_);
    return v_k_7645_;
}
pub unsafe fn l_IO_TaskState_ctorElim___boxed(
    mut v_motive_7646_: *mut LeanObject,
    mut v_ctorIdx_7647_: *mut LeanObject,
    mut v_t_7648_: *mut LeanObject,
    mut v_h_7649_: *mut LeanObject,
    mut v_k_7650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_7651_: u8 = 0;
    let mut v_res_7652_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_7651_ = (lean_unbox(v_t_7648_) as u8);
    v_res_7652_ = l_IO_TaskState_ctorElim(
        v_motive_7646_,
        v_ctorIdx_7647_,
        v_t_boxed_7651_,
        v_h_7649_,
        v_k_7650_,
    );
    lean_dec(v_k_7650_);
    lean_dec(v_ctorIdx_7647_);
    return v_res_7652_;
}
pub unsafe fn l_IO_TaskState_waiting_elim___redArg(
    mut v_waiting_7653_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_waiting_7653_);
    return v_waiting_7653_;
}
pub unsafe fn l_IO_TaskState_waiting_elim___redArg___boxed(
    mut v_waiting_7654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7655_: *mut LeanObject = core::ptr::null_mut();
    v_res_7655_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_7654_);
    lean_dec(v_waiting_7654_);
    return v_res_7655_;
}
pub unsafe fn l_IO_TaskState_waiting_elim(
    mut v_motive_7656_: *mut LeanObject,
    mut v_t_7657_: u8,
    mut v_h_7658_: *mut LeanObject,
    mut v_waiting_7659_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_waiting_7659_);
    return v_waiting_7659_;
}
pub unsafe fn l_IO_TaskState_waiting_elim___boxed(
    mut v_motive_7660_: *mut LeanObject,
    mut v_t_7661_: *mut LeanObject,
    mut v_h_7662_: *mut LeanObject,
    mut v_waiting_7663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_7664_: u8 = 0;
    let mut v_res_7665_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_7664_ = (lean_unbox(v_t_7661_) as u8);
    v_res_7665_ =
        l_IO_TaskState_waiting_elim(v_motive_7660_, v_t_boxed_7664_, v_h_7662_, v_waiting_7663_);
    lean_dec(v_waiting_7663_);
    return v_res_7665_;
}
pub unsafe fn l_IO_TaskState_running_elim___redArg(
    mut v_running_7666_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_running_7666_);
    return v_running_7666_;
}
pub unsafe fn l_IO_TaskState_running_elim___redArg___boxed(
    mut v_running_7667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7668_: *mut LeanObject = core::ptr::null_mut();
    v_res_7668_ = l_IO_TaskState_running_elim___redArg(v_running_7667_);
    lean_dec(v_running_7667_);
    return v_res_7668_;
}
pub unsafe fn l_IO_TaskState_running_elim(
    mut v_motive_7669_: *mut LeanObject,
    mut v_t_7670_: u8,
    mut v_h_7671_: *mut LeanObject,
    mut v_running_7672_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_running_7672_);
    return v_running_7672_;
}
pub unsafe fn l_IO_TaskState_running_elim___boxed(
    mut v_motive_7673_: *mut LeanObject,
    mut v_t_7674_: *mut LeanObject,
    mut v_h_7675_: *mut LeanObject,
    mut v_running_7676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_7677_: u8 = 0;
    let mut v_res_7678_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_7677_ = (lean_unbox(v_t_7674_) as u8);
    v_res_7678_ =
        l_IO_TaskState_running_elim(v_motive_7673_, v_t_boxed_7677_, v_h_7675_, v_running_7676_);
    lean_dec(v_running_7676_);
    return v_res_7678_;
}
pub unsafe fn l_IO_TaskState_finished_elim___redArg(
    mut v_finished_7679_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_finished_7679_);
    return v_finished_7679_;
}
pub unsafe fn l_IO_TaskState_finished_elim___redArg___boxed(
    mut v_finished_7680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7681_: *mut LeanObject = core::ptr::null_mut();
    v_res_7681_ = l_IO_TaskState_finished_elim___redArg(v_finished_7680_);
    lean_dec(v_finished_7680_);
    return v_res_7681_;
}
pub unsafe fn l_IO_TaskState_finished_elim(
    mut v_motive_7682_: *mut LeanObject,
    mut v_t_7683_: u8,
    mut v_h_7684_: *mut LeanObject,
    mut v_finished_7685_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_finished_7685_);
    return v_finished_7685_;
}
pub unsafe fn l_IO_TaskState_finished_elim___boxed(
    mut v_motive_7686_: *mut LeanObject,
    mut v_t_7687_: *mut LeanObject,
    mut v_h_7688_: *mut LeanObject,
    mut v_finished_7689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_7690_: u8 = 0;
    let mut v_res_7691_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_7690_ = (lean_unbox(v_t_7687_) as u8);
    v_res_7691_ =
        l_IO_TaskState_finished_elim(v_motive_7686_, v_t_boxed_7690_, v_h_7688_, v_finished_7689_);
    lean_dec(v_finished_7689_);
    return v_res_7691_;
}
pub unsafe fn _init_l_IO_instInhabitedTaskState_default() -> u8 {
    let mut v___x_7692_: u8 = 0;
    v___x_7692_ = 0;
    return v___x_7692_;
}
pub unsafe fn _init_l_IO_instInhabitedTaskState() -> u8 {
    let mut v___x_7693_: u8 = 0;
    v___x_7693_ = 0;
    return v___x_7693_;
}
pub unsafe fn _init_l_IO_instReprTaskState_repr___closed__6() -> *mut LeanObject {
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    v___x_7703_ = lean_unsigned_to_nat(2);
    v___x_7704_ = lean_nat_to_int(v___x_7703_);
    return v___x_7704_;
}
pub unsafe fn _init_l_IO_instReprTaskState_repr___closed__7() -> *mut LeanObject {
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    v___x_7705_ = lean_unsigned_to_nat(1);
    v___x_7706_ = lean_nat_to_int(v___x_7705_);
    return v___x_7706_;
}
pub unsafe fn l_IO_instReprTaskState_repr(
    mut v_x_7707_: u8,
    mut v_prec_7708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: u8 = 0;
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: u8 = 0;
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: u8 = 0;
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: u8 = 0;
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: u8 = 0;
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: u8 = 0;
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_7707_ {
                0 => {
                    v___x_7730_ = lean_unsigned_to_nat(1024);
                    v___x_7731_ = lean_nat_dec_le(v___x_7730_, v_prec_7708_);
                    if v___x_7731_ == 0 {
                        v___x_7732_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_7710_ = v___x_7732_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7733_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_7710_ = v___x_7733_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_7734_ = lean_unsigned_to_nat(1024);
                    v___x_7735_ = lean_nat_dec_le(v___x_7734_, v_prec_7708_);
                    if v___x_7735_ == 0 {
                        v___x_7736_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_7717_ = v___x_7736_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7737_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_7717_ = v___x_7737_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_7738_ = lean_unsigned_to_nat(1024);
                    v___x_7739_ = lean_nat_dec_le(v___x_7738_, v_prec_7708_);
                    if v___x_7739_ == 0 {
                        v___x_7740_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_7724_ = v___x_7740_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7741_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_7724_ = v___x_7741_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_7711_ = l_IO_instReprTaskState_repr___closed__1;
                lean_inc(v___y_7710_);
                v___x_7712_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_7712_, 0, v___y_7710_);
                lean_ctor_set(v___x_7712_, 1, v___x_7711_);
                v___x_7713_ = 0;
                v___x_7714_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_7714_, 0, v___x_7712_);
                lean_ctor_set_uint8(
                    v___x_7714_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7713_,
                );
                v___x_7715_ = l_Repr_addAppParen(v___x_7714_, v_prec_7708_);
                return v___x_7715_;
            }
            2 => {
                v___x_7718_ = l_IO_instReprTaskState_repr___closed__3;
                lean_inc(v___y_7717_);
                v___x_7719_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_7719_, 0, v___y_7717_);
                lean_ctor_set(v___x_7719_, 1, v___x_7718_);
                v___x_7720_ = 0;
                v___x_7721_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_7721_, 0, v___x_7719_);
                lean_ctor_set_uint8(
                    v___x_7721_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7720_,
                );
                v___x_7722_ = l_Repr_addAppParen(v___x_7721_, v_prec_7708_);
                return v___x_7722_;
            }
            3 => {
                v___x_7725_ = l_IO_instReprTaskState_repr___closed__5;
                lean_inc(v___y_7724_);
                v___x_7726_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_7726_, 0, v___y_7724_);
                lean_ctor_set(v___x_7726_, 1, v___x_7725_);
                v___x_7727_ = 0;
                v___x_7728_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_7728_, 0, v___x_7726_);
                lean_ctor_set_uint8(
                    v___x_7728_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7727_,
                );
                v___x_7729_ = l_Repr_addAppParen(v___x_7728_, v_prec_7708_);
                return v___x_7729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_instReprTaskState_repr___boxed(
    mut v_x_7742_: *mut LeanObject,
    mut v_prec_7743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_7744_: u8 = 0;
    let mut v_res_7745_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_7744_ = (lean_unbox(v_x_7742_) as u8);
    v_res_7745_ = l_IO_instReprTaskState_repr(v_x_177__boxed_7744_, v_prec_7743_);
    lean_dec(v_prec_7743_);
    return v_res_7745_;
}
pub unsafe fn l_IO_TaskState_ofNat(mut v_n_7748_: *mut LeanObject) -> u8 {
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: u8 = 0;
    v___x_7749_ = lean_unsigned_to_nat(0);
    v___x_7750_ = lean_nat_dec_le(v_n_7748_, v___x_7749_);
    if v___x_7750_ == 0 {
        let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7752_: u8 = 0;
        v___x_7751_ = lean_unsigned_to_nat(1);
        v___x_7752_ = lean_nat_dec_le(v_n_7748_, v___x_7751_);
        if v___x_7752_ == 0 {
            let mut v___x_7753_: u8 = 0;
            v___x_7753_ = 2;
            return v___x_7753_;
        } else {
            let mut v___x_7754_: u8 = 0;
            v___x_7754_ = 1;
            return v___x_7754_;
        }
    } else {
        let mut v___x_7755_: u8 = 0;
        v___x_7755_ = 0;
        return v___x_7755_;
    }
}
pub unsafe fn l_IO_TaskState_ofNat___boxed(mut v_n_7756_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7757_: u8 = 0;
    let mut v_r_7758_: *mut LeanObject = core::ptr::null_mut();
    v_res_7757_ = l_IO_TaskState_ofNat(v_n_7756_);
    lean_dec(v_n_7756_);
    v_r_7758_ = lean_box((v_res_7757_) as usize);
    return v_r_7758_;
}
pub unsafe fn l_IO_instDecidableEqTaskState(mut v_x_7759_: u8, mut v_y_7760_: u8) -> u8 {
    let mut v___x_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: u8 = 0;
    v___x_7761_ = l_IO_TaskState_ctorIdx(v_x_7759_);
    v___x_7762_ = l_IO_TaskState_ctorIdx(v_y_7760_);
    v___x_7763_ = lean_nat_dec_eq(v___x_7761_, v___x_7762_);
    lean_dec(v___x_7762_);
    lean_dec(v___x_7761_);
    return v___x_7763_;
}
pub unsafe fn l_IO_instDecidableEqTaskState___boxed(
    mut v_x_7764_: *mut LeanObject,
    mut v_y_7765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_7766_: u8 = 0;
    let mut v_y_14__boxed_7767_: u8 = 0;
    let mut v_res_7768_: u8 = 0;
    let mut v_r_7769_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_7766_ = (lean_unbox(v_x_7764_) as u8);
    v_y_14__boxed_7767_ = (lean_unbox(v_y_7765_) as u8);
    v_res_7768_ = l_IO_instDecidableEqTaskState(v_x_13__boxed_7766_, v_y_14__boxed_7767_);
    v_r_7769_ = lean_box((v_res_7768_) as usize);
    return v_r_7769_;
}
pub unsafe fn l_IO_instOrdTaskState_ord(mut v_x_7770_: u8, mut v_y_7771_: u8) -> u8 {
    let mut v___x_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: u8 = 0;
    v___x_7772_ = l_IO_TaskState_ctorIdx(v_x_7770_);
    v___x_7773_ = l_IO_TaskState_ctorIdx(v_y_7771_);
    v___x_7774_ = lean_nat_dec_lt(v___x_7772_, v___x_7773_);
    if v___x_7774_ == 0 {
        let mut v___x_7775_: u8 = 0;
        v___x_7775_ = lean_nat_dec_eq(v___x_7772_, v___x_7773_);
        lean_dec(v___x_7773_);
        lean_dec(v___x_7772_);
        if v___x_7775_ == 0 {
            let mut v___x_7776_: u8 = 0;
            v___x_7776_ = 2;
            return v___x_7776_;
        } else {
            let mut v___x_7777_: u8 = 0;
            v___x_7777_ = 1;
            return v___x_7777_;
        }
    } else {
        let mut v___x_7778_: u8 = 0;
        lean_dec(v___x_7773_);
        lean_dec(v___x_7772_);
        v___x_7778_ = 0;
        return v___x_7778_;
    }
}
pub unsafe fn l_IO_instOrdTaskState_ord___boxed(
    mut v_x_7779_: *mut LeanObject,
    mut v_y_7780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_7781_: u8 = 0;
    let mut v_y_31__boxed_7782_: u8 = 0;
    let mut v_res_7783_: u8 = 0;
    let mut v_r_7784_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_7781_ = (lean_unbox(v_x_7779_) as u8);
    v_y_31__boxed_7782_ = (lean_unbox(v_y_7780_) as u8);
    v_res_7783_ = l_IO_instOrdTaskState_ord(v_x_30__boxed_7781_, v_y_31__boxed_7782_);
    v_r_7784_ = lean_box((v_res_7783_) as usize);
    return v_r_7784_;
}
pub unsafe fn _init_l_IO_instLTTaskState() -> *mut LeanObject {
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    v___x_7787_ = lean_box(0);
    return v___x_7787_;
}
pub unsafe fn _init_l_IO_instLETaskState() -> *mut LeanObject {
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    v___x_7788_ = lean_box(0);
    return v___x_7788_;
}
pub unsafe fn l_IO_instMinTaskState___lam__0(mut v_x_7789_: u8, mut v_y_7790_: u8) -> u8 {
    let mut v___x_7791_: u8 = 0;
    v___x_7791_ = l_IO_instOrdTaskState_ord(v_x_7789_, v_y_7790_);
    if v___x_7791_ == 2 {
        return v_y_7790_;
    } else {
        return v_x_7789_;
    }
}
pub unsafe fn l_IO_instMinTaskState___lam__0___boxed(
    mut v_x_7792_: *mut LeanObject,
    mut v_y_7793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_7794_: u8 = 0;
    let mut v_y_boxed_7795_: u8 = 0;
    let mut v_res_7796_: u8 = 0;
    let mut v_r_7797_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_7794_ = (lean_unbox(v_x_7792_) as u8);
    v_y_boxed_7795_ = (lean_unbox(v_y_7793_) as u8);
    v_res_7796_ = l_IO_instMinTaskState___lam__0(v_x_boxed_7794_, v_y_boxed_7795_);
    v_r_7797_ = lean_box((v_res_7796_) as usize);
    return v_r_7797_;
}
pub unsafe fn l_IO_instMaxTaskState___lam__0(mut v_x_7800_: u8, mut v_y_7801_: u8) -> u8 {
    let mut v___x_7802_: u8 = 0;
    v___x_7802_ = l_IO_instOrdTaskState_ord(v_x_7800_, v_y_7801_);
    if v___x_7802_ == 2 {
        return v_x_7800_;
    } else {
        return v_y_7801_;
    }
}
pub unsafe fn l_IO_instMaxTaskState___lam__0___boxed(
    mut v_x_7803_: *mut LeanObject,
    mut v_y_7804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_7805_: u8 = 0;
    let mut v_y_boxed_7806_: u8 = 0;
    let mut v_res_7807_: u8 = 0;
    let mut v_r_7808_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_7805_ = (lean_unbox(v_x_7803_) as u8);
    v_y_boxed_7806_ = (lean_unbox(v_y_7804_) as u8);
    v_res_7807_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_7805_, v_y_boxed_7806_);
    v_r_7808_ = lean_box((v_res_7807_) as usize);
    return v_r_7808_;
}
pub unsafe fn l_IO_TaskState_toString(mut v_x_7814_: u8) -> *mut LeanObject {
    match v_x_7814_ {
        0 => {
            let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
            v___x_7815_ = l_IO_TaskState_toString___closed__0;
            return v___x_7815_;
        }
        1 => {
            let mut v___x_7816_: *mut LeanObject = core::ptr::null_mut();
            v___x_7816_ = l_IO_TaskState_toString___closed__1;
            return v___x_7816_;
        }
        _ => {
            let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
            v___x_7817_ = l_IO_TaskState_toString___closed__2;
            return v___x_7817_;
        }
    }
}
pub unsafe fn l_IO_TaskState_toString___boxed(mut v_x_7818_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_31__boxed_7819_: u8 = 0;
    let mut v_res_7820_: *mut LeanObject = core::ptr::null_mut();
    v_x_31__boxed_7819_ = (lean_unbox(v_x_7818_) as u8);
    v_res_7820_ = l_IO_TaskState_toString(v_x_31__boxed_7819_);
    return v_res_7820_;
}
pub unsafe fn l_IO_getTaskState___boxed(
    mut v_00_u03b1_7826_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7827_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7829_: u8 = 0;
    let mut v_r_7830_: *mut LeanObject = core::ptr::null_mut();
    v_res_7829_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_7827_);
    lean_dec_ref(v_a_00___x40___internal___hyg_7827_);
    v_r_7830_ = lean_box((v_res_7829_) as usize);
    return v_r_7830_;
}
pub unsafe fn l_IO_hasFinished___redArg(mut v_task_7831_: *mut LeanObject) -> u8 {
    let mut v___x_7833_: u8 = 0;
    v___x_7833_ = lean_io_get_task_state(v_task_7831_);
    if v___x_7833_ == 2 {
        let mut v___x_7834_: u8 = 0;
        v___x_7834_ = 1;
        return v___x_7834_;
    } else {
        let mut v___x_7835_: u8 = 0;
        v___x_7835_ = 0;
        return v___x_7835_;
    }
}
pub unsafe fn l_IO_hasFinished___redArg___boxed(
    mut v_task_7836_: *mut LeanObject,
    mut v_a_7837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7838_: u8 = 0;
    let mut v_r_7839_: *mut LeanObject = core::ptr::null_mut();
    v_res_7838_ = l_IO_hasFinished___redArg(v_task_7836_);
    lean_dec_ref(v_task_7836_);
    v_r_7839_ = lean_box((v_res_7838_) as usize);
    return v_r_7839_;
}
pub unsafe fn l_IO_hasFinished(
    mut v_00_u03b1_7840_: *mut LeanObject,
    mut v_task_7841_: *mut LeanObject,
) -> u8 {
    let mut v___x_7843_: u8 = 0;
    v___x_7843_ = lean_io_get_task_state(v_task_7841_);
    if v___x_7843_ == 2 {
        let mut v___x_7844_: u8 = 0;
        v___x_7844_ = 1;
        return v___x_7844_;
    } else {
        let mut v___x_7845_: u8 = 0;
        v___x_7845_ = 0;
        return v___x_7845_;
    }
}
pub unsafe fn l_IO_hasFinished___boxed(
    mut v_00_u03b1_7846_: *mut LeanObject,
    mut v_task_7847_: *mut LeanObject,
    mut v_a_7848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7849_: u8 = 0;
    let mut v_r_7850_: *mut LeanObject = core::ptr::null_mut();
    v_res_7849_ = l_IO_hasFinished(v_00_u03b1_7846_, v_task_7847_);
    lean_dec_ref(v_task_7847_);
    v_r_7850_ = lean_box((v_res_7849_) as usize);
    return v_r_7850_;
}
pub unsafe fn l_IO_wait___boxed(
    mut v_00_u03b1_7854_: *mut LeanObject,
    mut v_t_7855_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7857_: *mut LeanObject = core::ptr::null_mut();
    v_res_7857_ = lean_io_wait(v_t_7855_);
    return v_res_7857_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    v___x_7884_ = l_IO_waitAny___auto__1___closed__10;
    v___x_7885_ = l_Lean_mkAtom(v___x_7884_);
    return v___x_7885_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut LeanObject = core::ptr::null_mut();
    v___x_7886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__12_once),
        _init_l_IO_waitAny___auto__1___closed__12,
    );
    v___x_7887_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7888_ = lean_array_push(v___x_7887_, v___x_7886_);
    return v___x_7888_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    v___x_7897_ = l_IO_waitAny___auto__1___closed__17;
    v___x_7898_ = lean_string_utf8_byte_size(v___x_7897_);
    return v___x_7898_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut LeanObject = core::ptr::null_mut();
    v___x_7899_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__18_once),
        _init_l_IO_waitAny___auto__1___closed__18,
    );
    v___x_7900_ = lean_unsigned_to_nat(0);
    v___x_7901_ = l_IO_waitAny___auto__1___closed__17;
    v___x_7902_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7902_, 0, v___x_7901_);
    lean_ctor_set(v___x_7902_, 1, v___x_7900_);
    lean_ctor_set(v___x_7902_, 2, v___x_7899_);
    return v___x_7902_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut LeanObject = core::ptr::null_mut();
    v___x_7908_ = lean_box(0);
    v___x_7909_ = l_IO_waitAny___auto__1___closed__22;
    v___x_7910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__19_once),
        _init_l_IO_waitAny___auto__1___closed__19,
    );
    v___x_7911_ = lean_box(2);
    v___x_7912_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_7912_, 0, v___x_7911_);
    lean_ctor_set(v___x_7912_, 1, v___x_7910_);
    lean_ctor_set(v___x_7912_, 2, v___x_7909_);
    lean_ctor_set(v___x_7912_, 3, v___x_7908_);
    return v___x_7912_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    v___x_7913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__23_once),
        _init_l_IO_waitAny___auto__1___closed__23,
    );
    v___x_7914_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7915_ = lean_array_push(v___x_7914_, v___x_7913_);
    return v___x_7915_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7924_: *mut LeanObject = core::ptr::null_mut();
    v___x_7923_ = l_IO_waitAny___auto__1___closed__27;
    v___x_7924_ = l_Lean_mkAtom(v___x_7923_);
    return v___x_7924_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7927_: *mut LeanObject = core::ptr::null_mut();
    v___x_7925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__28_once),
        _init_l_IO_waitAny___auto__1___closed__28,
    );
    v___x_7926_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7927_ = lean_array_push(v___x_7926_, v___x_7925_);
    return v___x_7927_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    v___x_7928_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__29_once),
        _init_l_IO_waitAny___auto__1___closed__29,
    );
    v___x_7929_ = l_IO_waitAny___auto__1___closed__26;
    v___x_7930_ = lean_box(2);
    v___x_7931_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7931_, 0, v___x_7930_);
    lean_ctor_set(v___x_7931_, 1, v___x_7929_);
    lean_ctor_set(v___x_7931_, 2, v___x_7928_);
    return v___x_7931_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__31() -> *mut LeanObject {
    let mut v___x_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
    v___x_7932_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__30_once),
        _init_l_IO_waitAny___auto__1___closed__30,
    );
    v___x_7933_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7934_ = lean_array_push(v___x_7933_, v___x_7932_);
    return v___x_7934_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__32() -> *mut LeanObject {
    let mut v___x_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: *mut LeanObject = core::ptr::null_mut();
    v___x_7935_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__31_once),
        _init_l_IO_waitAny___auto__1___closed__31,
    );
    v___x_7936_ = l_IO_waitAny___auto__1___closed__9;
    v___x_7937_ = lean_box(2);
    v___x_7938_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7938_, 0, v___x_7937_);
    lean_ctor_set(v___x_7938_, 1, v___x_7936_);
    lean_ctor_set(v___x_7938_, 2, v___x_7935_);
    return v___x_7938_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__33() -> *mut LeanObject {
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7941_: *mut LeanObject = core::ptr::null_mut();
    v___x_7939_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__32_once),
        _init_l_IO_waitAny___auto__1___closed__32,
    );
    v___x_7940_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__24_once),
        _init_l_IO_waitAny___auto__1___closed__24,
    );
    v___x_7941_ = lean_array_push(v___x_7940_, v___x_7939_);
    return v___x_7941_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__34() -> *mut LeanObject {
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    v___x_7942_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__33_once),
        _init_l_IO_waitAny___auto__1___closed__33,
    );
    v___x_7943_ = l_IO_waitAny___auto__1___closed__16;
    v___x_7944_ = lean_box(2);
    v___x_7945_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7945_, 0, v___x_7944_);
    lean_ctor_set(v___x_7945_, 1, v___x_7943_);
    lean_ctor_set(v___x_7945_, 2, v___x_7942_);
    return v___x_7945_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__35() -> *mut LeanObject {
    let mut v___x_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    v___x_7946_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__34_once),
        _init_l_IO_waitAny___auto__1___closed__34,
    );
    v___x_7947_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__13_once),
        _init_l_IO_waitAny___auto__1___closed__13,
    );
    v___x_7948_ = lean_array_push(v___x_7947_, v___x_7946_);
    return v___x_7948_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__36() -> *mut LeanObject {
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut LeanObject = core::ptr::null_mut();
    v___x_7949_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__35_once),
        _init_l_IO_waitAny___auto__1___closed__35,
    );
    v___x_7950_ = l_IO_waitAny___auto__1___closed__11;
    v___x_7951_ = lean_box(2);
    v___x_7952_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7952_, 0, v___x_7951_);
    lean_ctor_set(v___x_7952_, 1, v___x_7950_);
    lean_ctor_set(v___x_7952_, 2, v___x_7949_);
    return v___x_7952_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__37() -> *mut LeanObject {
    let mut v___x_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut LeanObject = core::ptr::null_mut();
    v___x_7953_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__36_once),
        _init_l_IO_waitAny___auto__1___closed__36,
    );
    v___x_7954_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7955_ = lean_array_push(v___x_7954_, v___x_7953_);
    return v___x_7955_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__38() -> *mut LeanObject {
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    v___x_7956_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__37_once),
        _init_l_IO_waitAny___auto__1___closed__37,
    );
    v___x_7957_ = l_IO_waitAny___auto__1___closed__9;
    v___x_7958_ = lean_box(2);
    v___x_7959_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7959_, 0, v___x_7958_);
    lean_ctor_set(v___x_7959_, 1, v___x_7957_);
    lean_ctor_set(v___x_7959_, 2, v___x_7956_);
    return v___x_7959_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__39() -> *mut LeanObject {
    let mut v___x_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    v___x_7960_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__38_once),
        _init_l_IO_waitAny___auto__1___closed__38,
    );
    v___x_7961_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7962_ = lean_array_push(v___x_7961_, v___x_7960_);
    return v___x_7962_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__40() -> *mut LeanObject {
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    v___x_7963_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__39_once),
        _init_l_IO_waitAny___auto__1___closed__39,
    );
    v___x_7964_ = l_IO_waitAny___auto__1___closed__7;
    v___x_7965_ = lean_box(2);
    v___x_7966_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7966_, 0, v___x_7965_);
    lean_ctor_set(v___x_7966_, 1, v___x_7964_);
    lean_ctor_set(v___x_7966_, 2, v___x_7963_);
    return v___x_7966_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__41() -> *mut LeanObject {
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    v___x_7967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__40_once),
        _init_l_IO_waitAny___auto__1___closed__40,
    );
    v___x_7968_ = l_IO_waitAny___auto__1___closed__5;
    v___x_7969_ = lean_array_push(v___x_7968_, v___x_7967_);
    return v___x_7969_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1___closed__42() -> *mut LeanObject {
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    v___x_7970_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__41_once),
        _init_l_IO_waitAny___auto__1___closed__41,
    );
    v___x_7971_ = l_IO_waitAny___auto__1___closed__4;
    v___x_7972_ = lean_box(2);
    v___x_7973_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_7973_, 0, v___x_7972_);
    lean_ctor_set(v___x_7973_, 1, v___x_7971_);
    lean_ctor_set(v___x_7973_, 2, v___x_7970_);
    return v___x_7973_;
}
pub unsafe fn _init_l_IO_waitAny___auto__1() -> *mut LeanObject {
    let mut v___x_7974_: *mut LeanObject = core::ptr::null_mut();
    v___x_7974_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__42_once),
        _init_l_IO_waitAny___auto__1___closed__42,
    );
    return v___x_7974_;
}
pub unsafe fn l_IO_waitAny___boxed(
    mut v_00_u03b1_7979_: *mut LeanObject,
    mut v_tasks_7980_: *mut LeanObject,
    mut v_h_7981_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7983_: *mut LeanObject = core::ptr::null_mut();
    v_res_7983_ = lean_io_wait_any(v_tasks_7980_);
    lean_dec(v_tasks_7980_);
    return v_res_7983_;
}
pub unsafe fn _init_l_IO_waitAny_x27___auto__1() -> *mut LeanObject {
    let mut v___x_7984_: *mut LeanObject = core::ptr::null_mut();
    v___x_7984_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_IO_waitAny___auto__1___closed__42_once),
        _init_l_IO_waitAny___auto__1___closed__42,
    );
    return v___x_7984_;
}
pub unsafe fn l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(
    mut v___x_7985_: *mut LeanObject,
    mut v_a_7986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
    v___x_7987_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7987_, 0, v___x_7985_);
    lean_ctor_set(v___x_7987_, 1, v_a_7986_);
    return v___x_7987_;
}
pub unsafe fn l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(
    mut v_a_7988_: *mut LeanObject,
    mut v_a_7989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: u8 = 0;
    let mut v___x_7997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7988_) == 0 {
                    v___x_7990_ = lean_array_to_list(v_a_7989_);
                    return v___x_7990_;
                } else {
                    v_head_7991_ = lean_ctor_get(v_a_7988_, 0);
                    lean_inc(v_head_7991_);
                    v_tail_7992_ = lean_ctor_get(v_a_7988_, 1);
                    lean_inc(v_tail_7992_);
                    lean_dec_ref_known(v_a_7988_, 2);
                    v___x_7993_ = lean_array_get_size(v_a_7989_);
                    v___f_7994_ = lean_alloc_closure(
                        l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_7994_, 0, v___x_7993_);
                    v___x_7995_ = lean_unsigned_to_nat(0);
                    v___x_7996_ = 1;
                    v___x_7997_ =
                        lean_task_map(v___f_7994_, v_head_7991_, v___x_7995_, v___x_7996_);
                    v___x_7998_ = lean_array_push(v_a_7989_, v___x_7997_);
                    v_a_7988_ = v_tail_7992_;
                    v_a_7989_ = v___x_7998_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_waitAny_x27___redArg(mut v_tasks_8002_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8011_: u8 = 0;
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8004_ = l_IO_waitAny_x27___redArg___closed__0;
                lean_inc(v_tasks_8002_);
                v___x_8005_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(
                    v_tasks_8002_,
                    v___x_8004_,
                );
                v___x_8006_ = lean_io_wait_any(v___x_8005_);
                lean_dec(v___x_8005_);
                v_fst_8007_ = lean_ctor_get(v___x_8006_, 0);
                v_snd_8008_ = lean_ctor_get(v___x_8006_, 1);
                v_isSharedCheck_8016_ = (!lean_is_exclusive(v___x_8006_)) as u8;
                if v_isSharedCheck_8016_ == 0 {
                    v___x_8010_ = v___x_8006_;
                    v_isShared_8011_ = v_isSharedCheck_8016_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8008_);
                    lean_inc(v_fst_8007_);
                    lean_dec(v___x_8006_);
                    v___x_8010_ = lean_box(0);
                    v_isShared_8011_ = v_isSharedCheck_8016_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_tasks_8002_);
                v___x_8012_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
                    lean_box(0),
                    v_tasks_8002_,
                    v_tasks_8002_,
                    v_fst_8007_,
                    v___x_8004_,
                );
                lean_dec(v_tasks_8002_);
                if v_isShared_8011_ == 0 {
                    lean_ctor_set(v___x_8010_, 1, v___x_8012_);
                    lean_ctor_set(v___x_8010_, 0, v_snd_8008_);
                    v___x_8014_ = v___x_8010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8015_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8015_, 0, v_snd_8008_);
                    lean_ctor_set(v_reuseFailAlloc_8015_, 1, v___x_8012_);
                    v___x_8014_ = v_reuseFailAlloc_8015_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_waitAny_x27___redArg___boxed(
    mut v_tasks_8017_: *mut LeanObject,
    mut v_a_8018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8019_: *mut LeanObject = core::ptr::null_mut();
    v_res_8019_ = l_IO_waitAny_x27___redArg(v_tasks_8017_);
    return v_res_8019_;
}
pub unsafe fn l_IO_waitAny_x27(
    mut v_00_u03b1_8020_: *mut LeanObject,
    mut v_tasks_8021_: *mut LeanObject,
    mut v_h_8022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8024_: *mut LeanObject = core::ptr::null_mut();
    v___x_8024_ = l_IO_waitAny_x27___redArg(v_tasks_8021_);
    return v___x_8024_;
}
pub unsafe fn l_IO_waitAny_x27___boxed(
    mut v_00_u03b1_8025_: *mut LeanObject,
    mut v_tasks_8026_: *mut LeanObject,
    mut v_h_8027_: *mut LeanObject,
    mut v_a_8028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8029_: *mut LeanObject = core::ptr::null_mut();
    v_res_8029_ = l_IO_waitAny_x27(v_00_u03b1_8025_, v_tasks_8026_, v_h_8027_);
    return v_res_8029_;
}
pub unsafe fn l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(
    mut v_00_u03b1_8030_: *mut LeanObject,
    mut v_a_8031_: *mut LeanObject,
    mut v_a_8032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8033_: *mut LeanObject = core::ptr::null_mut();
    v___x_8033_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_8031_, v_a_8032_);
    return v___x_8033_;
}
pub unsafe fn l_IO_getNumHeartbeats___boxed(
    mut v_a_00___x40___internal___hyg_8035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8036_: *mut LeanObject = core::ptr::null_mut();
    v_res_8036_ = lean_io_get_num_heartbeats();
    return v_res_8036_;
}
pub unsafe fn l_IO_setNumHeartbeats___boxed(
    mut v_count_8039_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8041_: *mut LeanObject = core::ptr::null_mut();
    v_res_8041_ = lean_io_set_heartbeats(v_count_8039_);
    return v_res_8041_;
}
pub unsafe fn l_IO_addHeartbeats(mut v_count_8042_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8046_: *mut LeanObject = core::ptr::null_mut();
    v___x_8044_ = lean_io_get_num_heartbeats();
    v___x_8045_ = lean_nat_add(v___x_8044_, v_count_8042_);
    lean_dec(v___x_8044_);
    v___x_8046_ = lean_io_set_heartbeats(v___x_8045_);
    return v___x_8046_;
}
pub unsafe fn l_IO_addHeartbeats___boxed(
    mut v_count_8047_: *mut LeanObject,
    mut v_a_8048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8049_: *mut LeanObject = core::ptr::null_mut();
    v_res_8049_ = l_IO_addHeartbeats(v_count_8047_);
    lean_dec(v_count_8047_);
    return v_res_8049_;
}
pub unsafe fn l_IO_FS_Mode_ctorIdx(mut v_x_8050_: u8) -> *mut LeanObject {
    match v_x_8050_ {
        0 => {
            let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
            v___x_8051_ = lean_unsigned_to_nat(0);
            return v___x_8051_;
        }
        1 => {
            let mut v___x_8052_: *mut LeanObject = core::ptr::null_mut();
            v___x_8052_ = lean_unsigned_to_nat(1);
            return v___x_8052_;
        }
        2 => {
            let mut v___x_8053_: *mut LeanObject = core::ptr::null_mut();
            v___x_8053_ = lean_unsigned_to_nat(2);
            return v___x_8053_;
        }
        3 => {
            let mut v___x_8054_: *mut LeanObject = core::ptr::null_mut();
            v___x_8054_ = lean_unsigned_to_nat(3);
            return v___x_8054_;
        }
        _ => {
            let mut v___x_8055_: *mut LeanObject = core::ptr::null_mut();
            v___x_8055_ = lean_unsigned_to_nat(4);
            return v___x_8055_;
        }
    }
}
pub unsafe fn l_IO_FS_Mode_ctorIdx___boxed(mut v_x_8056_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_8057_: u8 = 0;
    let mut v_res_8058_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_8057_ = (lean_unbox(v_x_8056_) as u8);
    v_res_8058_ = l_IO_FS_Mode_ctorIdx(v_x_boxed_8057_);
    return v_res_8058_;
}
pub unsafe fn l_IO_FS_Mode_toCtorIdx(mut v_x_8059_: u8) -> *mut LeanObject {
    let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
    v___x_8060_ = l_IO_FS_Mode_ctorIdx(v_x_8059_);
    return v___x_8060_;
}
pub unsafe fn l_IO_FS_Mode_toCtorIdx___boxed(mut v_x_8061_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_8062_: u8 = 0;
    let mut v_res_8063_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_8062_ = (lean_unbox(v_x_8061_) as u8);
    v_res_8063_ = l_IO_FS_Mode_toCtorIdx(v_x_4__boxed_8062_);
    return v_res_8063_;
}
pub unsafe fn l_IO_FS_Mode_ctorElim___redArg(mut v_k_8064_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_8064_);
    return v_k_8064_;
}
pub unsafe fn l_IO_FS_Mode_ctorElim___redArg___boxed(
    mut v_k_8065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8066_: *mut LeanObject = core::ptr::null_mut();
    v_res_8066_ = l_IO_FS_Mode_ctorElim___redArg(v_k_8065_);
    lean_dec(v_k_8065_);
    return v_res_8066_;
}
pub unsafe fn l_IO_FS_Mode_ctorElim(
    mut v_motive_8067_: *mut LeanObject,
    mut v_ctorIdx_8068_: *mut LeanObject,
    mut v_t_8069_: u8,
    mut v_h_8070_: *mut LeanObject,
    mut v_k_8071_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_8071_);
    return v_k_8071_;
}
pub unsafe fn l_IO_FS_Mode_ctorElim___boxed(
    mut v_motive_8072_: *mut LeanObject,
    mut v_ctorIdx_8073_: *mut LeanObject,
    mut v_t_8074_: *mut LeanObject,
    mut v_h_8075_: *mut LeanObject,
    mut v_k_8076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8077_: u8 = 0;
    let mut v_res_8078_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8077_ = (lean_unbox(v_t_8074_) as u8);
    v_res_8078_ = l_IO_FS_Mode_ctorElim(
        v_motive_8072_,
        v_ctorIdx_8073_,
        v_t_boxed_8077_,
        v_h_8075_,
        v_k_8076_,
    );
    lean_dec(v_k_8076_);
    lean_dec(v_ctorIdx_8073_);
    return v_res_8078_;
}
pub unsafe fn l_IO_FS_Mode_read_elim___redArg(
    mut v_read_8079_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_read_8079_);
    return v_read_8079_;
}
pub unsafe fn l_IO_FS_Mode_read_elim___redArg___boxed(
    mut v_read_8080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8081_: *mut LeanObject = core::ptr::null_mut();
    v_res_8081_ = l_IO_FS_Mode_read_elim___redArg(v_read_8080_);
    lean_dec(v_read_8080_);
    return v_res_8081_;
}
pub unsafe fn l_IO_FS_Mode_read_elim(
    mut v_motive_8082_: *mut LeanObject,
    mut v_t_8083_: u8,
    mut v_h_8084_: *mut LeanObject,
    mut v_read_8085_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_read_8085_);
    return v_read_8085_;
}
pub unsafe fn l_IO_FS_Mode_read_elim___boxed(
    mut v_motive_8086_: *mut LeanObject,
    mut v_t_8087_: *mut LeanObject,
    mut v_h_8088_: *mut LeanObject,
    mut v_read_8089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8090_: u8 = 0;
    let mut v_res_8091_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8090_ = (lean_unbox(v_t_8087_) as u8);
    v_res_8091_ = l_IO_FS_Mode_read_elim(v_motive_8086_, v_t_boxed_8090_, v_h_8088_, v_read_8089_);
    lean_dec(v_read_8089_);
    return v_res_8091_;
}
pub unsafe fn l_IO_FS_Mode_write_elim___redArg(
    mut v_write_8092_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_write_8092_);
    return v_write_8092_;
}
pub unsafe fn l_IO_FS_Mode_write_elim___redArg___boxed(
    mut v_write_8093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8094_: *mut LeanObject = core::ptr::null_mut();
    v_res_8094_ = l_IO_FS_Mode_write_elim___redArg(v_write_8093_);
    lean_dec(v_write_8093_);
    return v_res_8094_;
}
pub unsafe fn l_IO_FS_Mode_write_elim(
    mut v_motive_8095_: *mut LeanObject,
    mut v_t_8096_: u8,
    mut v_h_8097_: *mut LeanObject,
    mut v_write_8098_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_write_8098_);
    return v_write_8098_;
}
pub unsafe fn l_IO_FS_Mode_write_elim___boxed(
    mut v_motive_8099_: *mut LeanObject,
    mut v_t_8100_: *mut LeanObject,
    mut v_h_8101_: *mut LeanObject,
    mut v_write_8102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8103_: u8 = 0;
    let mut v_res_8104_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8103_ = (lean_unbox(v_t_8100_) as u8);
    v_res_8104_ =
        l_IO_FS_Mode_write_elim(v_motive_8099_, v_t_boxed_8103_, v_h_8101_, v_write_8102_);
    lean_dec(v_write_8102_);
    return v_res_8104_;
}
pub unsafe fn l_IO_FS_Mode_writeNew_elim___redArg(
    mut v_writeNew_8105_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_writeNew_8105_);
    return v_writeNew_8105_;
}
pub unsafe fn l_IO_FS_Mode_writeNew_elim___redArg___boxed(
    mut v_writeNew_8106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8107_: *mut LeanObject = core::ptr::null_mut();
    v_res_8107_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_8106_);
    lean_dec(v_writeNew_8106_);
    return v_res_8107_;
}
pub unsafe fn l_IO_FS_Mode_writeNew_elim(
    mut v_motive_8108_: *mut LeanObject,
    mut v_t_8109_: u8,
    mut v_h_8110_: *mut LeanObject,
    mut v_writeNew_8111_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_writeNew_8111_);
    return v_writeNew_8111_;
}
pub unsafe fn l_IO_FS_Mode_writeNew_elim___boxed(
    mut v_motive_8112_: *mut LeanObject,
    mut v_t_8113_: *mut LeanObject,
    mut v_h_8114_: *mut LeanObject,
    mut v_writeNew_8115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8116_: u8 = 0;
    let mut v_res_8117_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8116_ = (lean_unbox(v_t_8113_) as u8);
    v_res_8117_ =
        l_IO_FS_Mode_writeNew_elim(v_motive_8112_, v_t_boxed_8116_, v_h_8114_, v_writeNew_8115_);
    lean_dec(v_writeNew_8115_);
    return v_res_8117_;
}
pub unsafe fn l_IO_FS_Mode_readWrite_elim___redArg(
    mut v_readWrite_8118_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_readWrite_8118_);
    return v_readWrite_8118_;
}
pub unsafe fn l_IO_FS_Mode_readWrite_elim___redArg___boxed(
    mut v_readWrite_8119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8120_: *mut LeanObject = core::ptr::null_mut();
    v_res_8120_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_8119_);
    lean_dec(v_readWrite_8119_);
    return v_res_8120_;
}
pub unsafe fn l_IO_FS_Mode_readWrite_elim(
    mut v_motive_8121_: *mut LeanObject,
    mut v_t_8122_: u8,
    mut v_h_8123_: *mut LeanObject,
    mut v_readWrite_8124_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_readWrite_8124_);
    return v_readWrite_8124_;
}
pub unsafe fn l_IO_FS_Mode_readWrite_elim___boxed(
    mut v_motive_8125_: *mut LeanObject,
    mut v_t_8126_: *mut LeanObject,
    mut v_h_8127_: *mut LeanObject,
    mut v_readWrite_8128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8129_: u8 = 0;
    let mut v_res_8130_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8129_ = (lean_unbox(v_t_8126_) as u8);
    v_res_8130_ = l_IO_FS_Mode_readWrite_elim(
        v_motive_8125_,
        v_t_boxed_8129_,
        v_h_8127_,
        v_readWrite_8128_,
    );
    lean_dec(v_readWrite_8128_);
    return v_res_8130_;
}
pub unsafe fn l_IO_FS_Mode_append_elim___redArg(
    mut v_append_8131_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_append_8131_);
    return v_append_8131_;
}
pub unsafe fn l_IO_FS_Mode_append_elim___redArg___boxed(
    mut v_append_8132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8133_: *mut LeanObject = core::ptr::null_mut();
    v_res_8133_ = l_IO_FS_Mode_append_elim___redArg(v_append_8132_);
    lean_dec(v_append_8132_);
    return v_res_8133_;
}
pub unsafe fn l_IO_FS_Mode_append_elim(
    mut v_motive_8134_: *mut LeanObject,
    mut v_t_8135_: u8,
    mut v_h_8136_: *mut LeanObject,
    mut v_append_8137_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_append_8137_);
    return v_append_8137_;
}
pub unsafe fn l_IO_FS_Mode_append_elim___boxed(
    mut v_motive_8138_: *mut LeanObject,
    mut v_t_8139_: *mut LeanObject,
    mut v_h_8140_: *mut LeanObject,
    mut v_append_8141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8142_: u8 = 0;
    let mut v_res_8143_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8142_ = (lean_unbox(v_t_8139_) as u8);
    v_res_8143_ =
        l_IO_FS_Mode_append_elim(v_motive_8138_, v_t_boxed_8142_, v_h_8140_, v_append_8141_);
    lean_dec(v_append_8141_);
    return v_res_8143_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__0() -> *mut LeanObject {
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut LeanObject = core::ptr::null_mut();
    v___x_8148_ = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
    v___x_8149_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8149_, 0, v___x_8148_);
    return v___x_8149_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__0___boxed(
    mut v___y_8150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8151_: *mut LeanObject = core::ptr::null_mut();
    v_res_8151_ = l_IO_FS_instInhabitedStream_default___lam__0();
    return v_res_8151_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__1() -> *mut LeanObject {
    let mut v___x_8153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    v___x_8153_ = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
    v___x_8154_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8154_, 0, v___x_8153_);
    return v___x_8154_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__1___boxed(
    mut v___y_8155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8156_: *mut LeanObject = core::ptr::null_mut();
    v_res_8156_ = l_IO_FS_instInhabitedStream_default___lam__1();
    return v_res_8156_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__2(
    mut v_x_8157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    v___x_8159_ = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
    v___x_8160_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8160_, 0, v___x_8159_);
    return v___x_8160_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__2___boxed(
    mut v_x_8161_: *mut LeanObject,
    mut v___y_8162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8163_: *mut LeanObject = core::ptr::null_mut();
    v_res_8163_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_8161_);
    lean_dec_ref(v_x_8161_);
    return v_res_8163_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__3(
    mut v_x_8164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    v___x_8166_ = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
    v___x_8167_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8167_, 0, v___x_8166_);
    return v___x_8167_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__3___boxed(
    mut v_x_8168_: *mut LeanObject,
    mut v___y_8169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8170_: *mut LeanObject = core::ptr::null_mut();
    v_res_8170_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_8168_);
    lean_dec_ref(v_x_8168_);
    return v_res_8170_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__4(
    mut v_x_8171_: usize,
) -> *mut LeanObject {
    let mut v___x_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8174_: *mut LeanObject = core::ptr::null_mut();
    v___x_8173_ = l_IO_FS_instInhabitedStream_default___lam__0___closed__1;
    v___x_8174_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8174_, 0, v___x_8173_);
    return v___x_8174_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__4___boxed(
    mut v_x_8175_: *mut LeanObject,
    mut v___y_8176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_193__boxed_8177_: usize = 0;
    let mut v_res_8178_: *mut LeanObject = core::ptr::null_mut();
    v_x_193__boxed_8177_ = lean_unbox_usize(v_x_8175_);
    lean_dec(v_x_8175_);
    v_res_8178_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_193__boxed_8177_);
    return v_res_8178_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__5(mut v___x_8179_: u8) -> u8 {
    return v___x_8179_;
}
pub unsafe fn l_IO_FS_instInhabitedStream_default___lam__5___boxed(
    mut v___x_8181_: *mut LeanObject,
    mut v___y_8182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_204__boxed_8183_: u8 = 0;
    let mut v_res_8184_: u8 = 0;
    let mut v_r_8185_: *mut LeanObject = core::ptr::null_mut();
    v___x_204__boxed_8183_ = (lean_unbox(v___x_8181_) as u8);
    v_res_8184_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_204__boxed_8183_);
    v_r_8185_ = lean_box((v_res_8184_) as usize);
    return v_r_8185_;
}
pub unsafe fn l_IO_getStdin___boxed(
    mut v_a_00___x40___internal___hyg_8204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8205_: *mut LeanObject = core::ptr::null_mut();
    v_res_8205_ = lean_get_stdin();
    return v_res_8205_;
}
pub unsafe fn l_IO_getStdout___boxed(
    mut v_a_00___x40___internal___hyg_8207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8208_: *mut LeanObject = core::ptr::null_mut();
    v_res_8208_ = lean_get_stdout();
    return v_res_8208_;
}
pub unsafe fn l_IO_getStderr___boxed(
    mut v_a_00___x40___internal___hyg_8210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8211_: *mut LeanObject = core::ptr::null_mut();
    v_res_8211_ = lean_get_stderr();
    return v_res_8211_;
}
pub unsafe fn l_IO_setStdin___boxed(
    mut v_a_00___x40___internal___hyg_8214_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8216_: *mut LeanObject = core::ptr::null_mut();
    v_res_8216_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_8214_);
    return v_res_8216_;
}
pub unsafe fn l_IO_setStdout___boxed(
    mut v_a_00___x40___internal___hyg_8219_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8221_: *mut LeanObject = core::ptr::null_mut();
    v_res_8221_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_8219_);
    return v_res_8221_;
}
pub unsafe fn l_IO_setStderr___boxed(
    mut v_a_00___x40___internal___hyg_8224_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8226_: *mut LeanObject = core::ptr::null_mut();
    v_res_8226_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_8224_);
    return v_res_8226_;
}
pub unsafe fn l_IO_iterate___redArg(
    mut v_a_8227_: *mut LeanObject,
    mut v_f_8228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8234_: u8 = 0;
    let mut v_val_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8241_: u8 = 0;
    let mut v_a_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8245_: u8 = 0;
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_f_8228_);
                v___x_8230_ = lean_apply_2(v_f_8228_, v_a_8227_, lean_box(0));
                if lean_obj_tag(v___x_8230_) == 0 {
                    v_a_8231_ = lean_ctor_get(v___x_8230_, 0);
                    v_isSharedCheck_8241_ = (!lean_is_exclusive(v___x_8230_)) as u8;
                    if v_isSharedCheck_8241_ == 0 {
                        v___x_8233_ = v___x_8230_;
                        v_isShared_8234_ = v_isSharedCheck_8241_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8231_);
                        lean_dec(v___x_8230_);
                        v___x_8233_ = lean_box(0);
                        v_isShared_8234_ = v_isSharedCheck_8241_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_8228_);
                    v_a_8242_ = lean_ctor_get(v___x_8230_, 0);
                    v_isSharedCheck_8249_ = (!lean_is_exclusive(v___x_8230_)) as u8;
                    if v_isSharedCheck_8249_ == 0 {
                        v___x_8244_ = v___x_8230_;
                        v_isShared_8245_ = v_isSharedCheck_8249_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8242_);
                        lean_dec(v___x_8230_);
                        v___x_8244_ = lean_box(0);
                        v_isShared_8245_ = v_isSharedCheck_8249_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_8231_) == 0 {
                    lean_del_object(v___x_8233_);
                    v_val_8235_ = lean_ctor_get(v_a_8231_, 0);
                    lean_inc(v_val_8235_);
                    lean_dec_ref_known(v_a_8231_, 1);
                    v_a_8227_ = v_val_8235_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_f_8228_);
                    v_val_8237_ = lean_ctor_get(v_a_8231_, 0);
                    lean_inc(v_val_8237_);
                    lean_dec_ref_known(v_a_8231_, 1);
                    if v_isShared_8234_ == 0 {
                        lean_ctor_set(v___x_8233_, 0, v_val_8237_);
                        v___x_8239_ = v___x_8233_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8240_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8240_, 0, v_val_8237_);
                        v___x_8239_ = v_reuseFailAlloc_8240_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8239_;
            }
            3 => {
                if v_isShared_8245_ == 0 {
                    v___x_8247_ = v___x_8244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 0, v_a_8242_);
                    v___x_8247_ = v_reuseFailAlloc_8248_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_iterate___redArg___boxed(
    mut v_a_8250_: *mut LeanObject,
    mut v_f_8251_: *mut LeanObject,
    mut v_a_8252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8253_: *mut LeanObject = core::ptr::null_mut();
    v_res_8253_ = l_IO_iterate___redArg(v_a_8250_, v_f_8251_);
    return v_res_8253_;
}
pub unsafe fn l_IO_iterate(
    mut v_00_u03b1_8254_: *mut LeanObject,
    mut v_00_u03b2_8255_: *mut LeanObject,
    mut v_a_8256_: *mut LeanObject,
    mut v_f_8257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    v___x_8259_ = l_IO_iterate___redArg(v_a_8256_, v_f_8257_);
    return v___x_8259_;
}
pub unsafe fn l_IO_iterate___boxed(
    mut v_00_u03b1_8260_: *mut LeanObject,
    mut v_00_u03b2_8261_: *mut LeanObject,
    mut v_a_8262_: *mut LeanObject,
    mut v_f_8263_: *mut LeanObject,
    mut v_a_8264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8265_: *mut LeanObject = core::ptr::null_mut();
    v_res_8265_ = l_IO_iterate(v_00_u03b1_8260_, v_00_u03b2_8261_, v_a_8262_, v_f_8263_);
    return v_res_8265_;
}
pub unsafe fn l_IO_FS_Handle_mk___boxed(
    mut v_fn_8269_: *mut LeanObject,
    mut v_mode_8270_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_8272_: u8 = 0;
    let mut v_res_8273_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_8272_ = (lean_unbox(v_mode_8270_) as u8);
    v_res_8273_ = lean_io_prim_handle_mk(v_fn_8269_, v_mode_boxed_8272_);
    lean_dec_ref(v_fn_8269_);
    return v_res_8273_;
}
pub unsafe fn l_IO_FS_Handle_lock___boxed(
    mut v_h_8277_: *mut LeanObject,
    mut v_exclusive_8278_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exclusive_boxed_8280_: u8 = 0;
    let mut v_res_8281_: *mut LeanObject = core::ptr::null_mut();
    v_exclusive_boxed_8280_ = (lean_unbox(v_exclusive_8278_) as u8);
    v_res_8281_ = lean_io_prim_handle_lock(v_h_8277_, v_exclusive_boxed_8280_);
    lean_dec(v_h_8277_);
    return v_res_8281_;
}
pub unsafe fn l_IO_FS_Handle_tryLock___boxed(
    mut v_h_8285_: *mut LeanObject,
    mut v_exclusive_8286_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exclusive_boxed_8288_: u8 = 0;
    let mut v_res_8289_: *mut LeanObject = core::ptr::null_mut();
    v_exclusive_boxed_8288_ = (lean_unbox(v_exclusive_8286_) as u8);
    v_res_8289_ = lean_io_prim_handle_try_lock(v_h_8285_, v_exclusive_boxed_8288_);
    lean_dec(v_h_8285_);
    return v_res_8289_;
}
pub unsafe fn l_IO_FS_Handle_unlock___boxed(
    mut v_h_8292_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8294_: *mut LeanObject = core::ptr::null_mut();
    v_res_8294_ = lean_io_prim_handle_unlock(v_h_8292_);
    lean_dec(v_h_8292_);
    return v_res_8294_;
}
pub unsafe fn l_IO_FS_Handle_isTty___boxed(
    mut v_h_8297_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8299_: u8 = 0;
    let mut v_r_8300_: *mut LeanObject = core::ptr::null_mut();
    v_res_8299_ = lean_io_prim_handle_is_tty(v_h_8297_);
    lean_dec(v_h_8297_);
    v_r_8300_ = lean_box((v_res_8299_) as usize);
    return v_r_8300_;
}
pub unsafe fn l_IO_FS_Handle_flush___boxed(
    mut v_h_8303_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8305_: *mut LeanObject = core::ptr::null_mut();
    v_res_8305_ = lean_io_prim_handle_flush(v_h_8303_);
    lean_dec(v_h_8303_);
    return v_res_8305_;
}
pub unsafe fn l_IO_FS_Handle_rewind___boxed(
    mut v_h_8308_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8310_: *mut LeanObject = core::ptr::null_mut();
    v_res_8310_ = lean_io_prim_handle_rewind(v_h_8308_);
    lean_dec(v_h_8308_);
    return v_res_8310_;
}
pub unsafe fn l_IO_FS_Handle_truncate___boxed(
    mut v_h_8313_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8315_: *mut LeanObject = core::ptr::null_mut();
    v_res_8315_ = lean_io_prim_handle_truncate(v_h_8313_);
    lean_dec(v_h_8313_);
    return v_res_8315_;
}
pub unsafe fn l_IO_FS_Handle_read___boxed(
    mut v_h_8319_: *mut LeanObject,
    mut v_bytes_8320_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bytes_boxed_8322_: usize = 0;
    let mut v_res_8323_: *mut LeanObject = core::ptr::null_mut();
    v_bytes_boxed_8322_ = lean_unbox_usize(v_bytes_8320_);
    lean_dec(v_bytes_8320_);
    v_res_8323_ = lean_io_prim_handle_read(v_h_8319_, v_bytes_boxed_8322_);
    lean_dec(v_h_8319_);
    return v_res_8323_;
}
pub unsafe fn l_IO_FS_Handle_write___boxed(
    mut v_h_8327_: *mut LeanObject,
    mut v_buffer_8328_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8330_: *mut LeanObject = core::ptr::null_mut();
    v_res_8330_ = lean_io_prim_handle_write(v_h_8327_, v_buffer_8328_);
    lean_dec_ref(v_buffer_8328_);
    lean_dec(v_h_8327_);
    return v_res_8330_;
}
pub unsafe fn l_IO_FS_Handle_getLine___boxed(
    mut v_h_8333_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8335_: *mut LeanObject = core::ptr::null_mut();
    v_res_8335_ = lean_io_prim_handle_get_line(v_h_8333_);
    lean_dec(v_h_8333_);
    return v_res_8335_;
}
pub unsafe fn l_IO_FS_Handle_putStr___boxed(
    mut v_h_8339_: *mut LeanObject,
    mut v_s_8340_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8342_: *mut LeanObject = core::ptr::null_mut();
    v_res_8342_ = lean_io_prim_handle_put_str(v_h_8339_, v_s_8340_);
    lean_dec_ref(v_s_8340_);
    lean_dec(v_h_8339_);
    return v_res_8342_;
}
pub unsafe fn l_IO_FS_realPath___boxed(
    mut v_fname_8345_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8347_: *mut LeanObject = core::ptr::null_mut();
    v_res_8347_ = lean_io_realpath(v_fname_8345_);
    return v_res_8347_;
}
pub unsafe fn l_IO_FS_removeFile___boxed(
    mut v_fname_8350_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8352_: *mut LeanObject = core::ptr::null_mut();
    v_res_8352_ = lean_io_remove_file(v_fname_8350_);
    lean_dec_ref(v_fname_8350_);
    return v_res_8352_;
}
pub unsafe fn l_IO_FS_removeDir___boxed(
    mut v_a_00___x40___internal___hyg_8355_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8357_: *mut LeanObject = core::ptr::null_mut();
    v_res_8357_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_8355_);
    lean_dec_ref(v_a_00___x40___internal___hyg_8355_);
    return v_res_8357_;
}
pub unsafe fn l_IO_FS_createDir___boxed(
    mut v_a_00___x40___internal___hyg_8360_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8362_: *mut LeanObject = core::ptr::null_mut();
    v_res_8362_ = lean_io_create_dir(v_a_00___x40___internal___hyg_8360_);
    lean_dec_ref(v_a_00___x40___internal___hyg_8360_);
    return v_res_8362_;
}
pub unsafe fn l_IO_FS_rename___boxed(
    mut v_old_8366_: *mut LeanObject,
    mut v_new_8367_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8369_: *mut LeanObject = core::ptr::null_mut();
    v_res_8369_ = lean_io_rename(v_old_8366_, v_new_8367_);
    lean_dec_ref(v_new_8367_);
    lean_dec_ref(v_old_8366_);
    return v_res_8369_;
}
pub unsafe fn l_IO_FS_hardLink___boxed(
    mut v_orig_8373_: *mut LeanObject,
    mut v_link_8374_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8376_: *mut LeanObject = core::ptr::null_mut();
    v_res_8376_ = lean_io_hard_link(v_orig_8373_, v_link_8374_);
    lean_dec_ref(v_link_8374_);
    lean_dec_ref(v_orig_8373_);
    return v_res_8376_;
}
pub unsafe fn l_IO_FS_createTempFile___boxed(
    mut v_a_00___x40___internal___hyg_8378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8379_: *mut LeanObject = core::ptr::null_mut();
    v_res_8379_ = lean_io_create_tempfile();
    return v_res_8379_;
}
pub unsafe fn l_IO_FS_createTempDir___boxed(
    mut v_a_00___x40___internal___hyg_8381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8382_: *mut LeanObject = core::ptr::null_mut();
    v_res_8382_ = lean_io_create_tempdir();
    return v_res_8382_;
}
pub unsafe fn l_IO_getEnv___boxed(
    mut v_var_8385_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_8386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8387_: *mut LeanObject = core::ptr::null_mut();
    v_res_8387_ = lean_io_getenv(v_var_8385_);
    lean_dec_ref(v_var_8385_);
    return v_res_8387_;
}
pub unsafe fn l_IO_appPath___boxed(
    mut v_a_00___x40___internal___hyg_8389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8390_: *mut LeanObject = core::ptr::null_mut();
    v_res_8390_ = lean_io_app_path();
    return v_res_8390_;
}
pub unsafe fn l_IO_currentDir___boxed(
    mut v_a_00___x40___internal___hyg_8392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8393_: *mut LeanObject = core::ptr::null_mut();
    v_res_8393_ = lean_io_current_dir();
    return v_res_8393_;
}
pub unsafe fn l_IO_FS_withFile___redArg(
    mut v_fn_8394_: *mut LeanObject,
    mut v_mode_8395_: u8,
    mut v_f_8396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8404_: u8 = 0;
    let mut v___x_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8398_ = lean_io_prim_handle_mk(v_fn_8394_, v_mode_8395_);
                if lean_obj_tag(v___x_8398_) == 0 {
                    v_a_8399_ = lean_ctor_get(v___x_8398_, 0);
                    lean_inc(v_a_8399_);
                    lean_dec_ref_known(v___x_8398_, 1);
                    v___x_8400_ = lean_apply_2(v_f_8396_, v_a_8399_, lean_box(0));
                    return v___x_8400_;
                } else {
                    lean_dec_ref(v_f_8396_);
                    v_a_8401_ = lean_ctor_get(v___x_8398_, 0);
                    v_isSharedCheck_8408_ = (!lean_is_exclusive(v___x_8398_)) as u8;
                    if v_isSharedCheck_8408_ == 0 {
                        v___x_8403_ = v___x_8398_;
                        v_isShared_8404_ = v_isSharedCheck_8408_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8401_);
                        lean_dec(v___x_8398_);
                        v___x_8403_ = lean_box(0);
                        v_isShared_8404_ = v_isSharedCheck_8408_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8404_ == 0 {
                    v___x_8406_ = v___x_8403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8407_, 0, v_a_8401_);
                    v___x_8406_ = v_reuseFailAlloc_8407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withFile___redArg___boxed(
    mut v_fn_8409_: *mut LeanObject,
    mut v_mode_8410_: *mut LeanObject,
    mut v_f_8411_: *mut LeanObject,
    mut v_a_8412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_8413_: u8 = 0;
    let mut v_res_8414_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_8413_ = (lean_unbox(v_mode_8410_) as u8);
    v_res_8414_ = l_IO_FS_withFile___redArg(v_fn_8409_, v_mode_boxed_8413_, v_f_8411_);
    lean_dec_ref(v_fn_8409_);
    return v_res_8414_;
}
pub unsafe fn l_IO_FS_withFile(
    mut v_00_u03b1_8415_: *mut LeanObject,
    mut v_fn_8416_: *mut LeanObject,
    mut v_mode_8417_: u8,
    mut v_f_8418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8426_: u8 = 0;
    let mut v___x_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8420_ = lean_io_prim_handle_mk(v_fn_8416_, v_mode_8417_);
                if lean_obj_tag(v___x_8420_) == 0 {
                    v_a_8421_ = lean_ctor_get(v___x_8420_, 0);
                    lean_inc(v_a_8421_);
                    lean_dec_ref_known(v___x_8420_, 1);
                    v___x_8422_ = lean_apply_2(v_f_8418_, v_a_8421_, lean_box(0));
                    return v___x_8422_;
                } else {
                    lean_dec_ref(v_f_8418_);
                    v_a_8423_ = lean_ctor_get(v___x_8420_, 0);
                    v_isSharedCheck_8430_ = (!lean_is_exclusive(v___x_8420_)) as u8;
                    if v_isSharedCheck_8430_ == 0 {
                        v___x_8425_ = v___x_8420_;
                        v_isShared_8426_ = v_isSharedCheck_8430_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8423_);
                        lean_dec(v___x_8420_);
                        v___x_8425_ = lean_box(0);
                        v_isShared_8426_ = v_isSharedCheck_8430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8426_ == 0 {
                    v___x_8428_ = v___x_8425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8429_, 0, v_a_8423_);
                    v___x_8428_ = v_reuseFailAlloc_8429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withFile___boxed(
    mut v_00_u03b1_8431_: *mut LeanObject,
    mut v_fn_8432_: *mut LeanObject,
    mut v_mode_8433_: *mut LeanObject,
    mut v_f_8434_: *mut LeanObject,
    mut v_a_8435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_8436_: u8 = 0;
    let mut v_res_8437_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_8436_ = (lean_unbox(v_mode_8433_) as u8);
    v_res_8437_ = l_IO_FS_withFile(v_00_u03b1_8431_, v_fn_8432_, v_mode_boxed_8436_, v_f_8434_);
    lean_dec_ref(v_fn_8432_);
    return v_res_8437_;
}
pub unsafe fn l_IO_FS_Handle_putStrLn(
    mut v_h_8438_: *mut LeanObject,
    mut v_s_8439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8441_: u32 = 0;
    let mut v___x_8442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8443_: *mut LeanObject = core::ptr::null_mut();
    v___x_8441_ = 10;
    v___x_8442_ = lean_string_push(v_s_8439_, v___x_8441_);
    v___x_8443_ = lean_io_prim_handle_put_str(v_h_8438_, v___x_8442_);
    lean_dec_ref(v___x_8442_);
    return v___x_8443_;
}
pub unsafe fn l_IO_FS_Handle_putStrLn___boxed(
    mut v_h_8444_: *mut LeanObject,
    mut v_s_8445_: *mut LeanObject,
    mut v_a_8446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8447_: *mut LeanObject = core::ptr::null_mut();
    v_res_8447_ = l_IO_FS_Handle_putStrLn(v_h_8444_, v_s_8445_);
    lean_dec(v_h_8444_);
    return v_res_8447_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(
    mut v_h_8448_: *mut LeanObject,
    mut v_acc_8449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8451_: usize = 0;
    let mut v___x_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8456_: u8 = 0;
    let mut v___x_8457_: u8 = 0;
    let mut v___x_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8451_ = 1024usize;
                v___x_8452_ = lean_io_prim_handle_read(v_h_8448_, v___x_8451_);
                if lean_obj_tag(v___x_8452_) == 0 {
                    v_a_8453_ = lean_ctor_get(v___x_8452_, 0);
                    v_isSharedCheck_8466_ = (!lean_is_exclusive(v___x_8452_)) as u8;
                    if v_isSharedCheck_8466_ == 0 {
                        v___x_8455_ = v___x_8452_;
                        v_isShared_8456_ = v_isSharedCheck_8466_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8453_);
                        lean_dec(v___x_8452_);
                        v___x_8455_ = lean_box(0);
                        v_isShared_8456_ = v_isSharedCheck_8466_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_acc_8449_);
                    return v___x_8452_;
                }
            }
            1 => {
                v___x_8457_ = l_ByteArray_isEmpty(v_a_8453_);
                if v___x_8457_ == 0 {
                    lean_del_object(v___x_8455_);
                    v___x_8458_ = lean_unsigned_to_nat(0);
                    v___x_8459_ = lean_byte_array_size(v_acc_8449_);
                    v___x_8460_ = lean_byte_array_size(v_a_8453_);
                    v___x_8461_ = lean_byte_array_copy_slice(
                        v_a_8453_,
                        v___x_8458_,
                        v_acc_8449_,
                        v___x_8459_,
                        v___x_8460_,
                        v___x_8457_,
                    );
                    lean_dec(v_a_8453_);
                    v_acc_8449_ = v___x_8461_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_8453_);
                    if v_isShared_8456_ == 0 {
                        lean_ctor_set(v___x_8455_, 0, v_acc_8449_);
                        v___x_8464_ = v___x_8455_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8465_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8465_, 0, v_acc_8449_);
                        v___x_8464_ = v_reuseFailAlloc_8465_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(
    mut v_h_8467_: *mut LeanObject,
    mut v_acc_8468_: *mut LeanObject,
    mut v_a_8469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8470_: *mut LeanObject = core::ptr::null_mut();
    v_res_8470_ =
        l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_8467_, v_acc_8468_);
    lean_dec(v_h_8467_);
    return v_res_8470_;
}
pub unsafe fn l_IO_FS_Handle_readBinToEndInto(
    mut v_h_8471_: *mut LeanObject,
    mut v_buf_8472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    v___x_8474_ =
        l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_8471_, v_buf_8472_);
    return v___x_8474_;
}
pub unsafe fn l_IO_FS_Handle_readBinToEndInto___boxed(
    mut v_h_8475_: *mut LeanObject,
    mut v_buf_8476_: *mut LeanObject,
    mut v_a_8477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8478_: *mut LeanObject = core::ptr::null_mut();
    v_res_8478_ = l_IO_FS_Handle_readBinToEndInto(v_h_8475_, v_buf_8476_);
    lean_dec(v_h_8475_);
    return v_res_8478_;
}
pub unsafe fn l_IO_FS_Handle_readBinToEnd(mut v_h_8479_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    v___x_8481_ = l_ByteArray_empty;
    v___x_8482_ =
        l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_8479_, v___x_8481_);
    return v___x_8482_;
}
pub unsafe fn l_IO_FS_Handle_readBinToEnd___boxed(
    mut v_h_8483_: *mut LeanObject,
    mut v_a_8484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8485_: *mut LeanObject = core::ptr::null_mut();
    v_res_8485_ = l_IO_FS_Handle_readBinToEnd(v_h_8483_);
    lean_dec(v_h_8483_);
    return v_res_8485_;
}
pub unsafe fn l_IO_FS_Handle_readToEnd(mut v_h_8489_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8495_: u8 = 0;
    let mut v___x_8496_: u8 = 0;
    let mut v___x_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8505_: u8 = 0;
    let mut v_a_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8509_: u8 = 0;
    let mut v___x_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8491_ = l_IO_FS_Handle_readBinToEnd(v_h_8489_);
                if lean_obj_tag(v___x_8491_) == 0 {
                    v_a_8492_ = lean_ctor_get(v___x_8491_, 0);
                    v_isSharedCheck_8505_ = (!lean_is_exclusive(v___x_8491_)) as u8;
                    if v_isSharedCheck_8505_ == 0 {
                        v___x_8494_ = v___x_8491_;
                        v_isShared_8495_ = v_isSharedCheck_8505_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8492_);
                        lean_dec(v___x_8491_);
                        v___x_8494_ = lean_box(0);
                        v_isShared_8495_ = v_isSharedCheck_8505_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8506_ = lean_ctor_get(v___x_8491_, 0);
                    v_isSharedCheck_8513_ = (!lean_is_exclusive(v___x_8491_)) as u8;
                    if v_isSharedCheck_8513_ == 0 {
                        v___x_8508_ = v___x_8491_;
                        v_isShared_8509_ = v_isSharedCheck_8513_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8506_);
                        lean_dec(v___x_8491_);
                        v___x_8508_ = lean_box(0);
                        v_isShared_8509_ = v_isSharedCheck_8513_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8496_ = lean_string_validate_utf8(v_a_8492_);
                if v___x_8496_ == 0 {
                    lean_dec(v_a_8492_);
                    v___x_8497_ = l_IO_FS_Handle_readToEnd___closed__1;
                    if v_isShared_8495_ == 0 {
                        lean_ctor_set_tag(v___x_8494_, 1);
                        lean_ctor_set(v___x_8494_, 0, v___x_8497_);
                        v___x_8499_ = v___x_8494_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8500_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8500_, 0, v___x_8497_);
                        v___x_8499_ = v_reuseFailAlloc_8500_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_8501_ = lean_string_from_utf8_unchecked(v_a_8492_);
                    if v_isShared_8495_ == 0 {
                        lean_ctor_set(v___x_8494_, 0, v___x_8501_);
                        v___x_8503_ = v___x_8494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8504_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8504_, 0, v___x_8501_);
                        v___x_8503_ = v_reuseFailAlloc_8504_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8499_;
            }
            3 => {
                return v___x_8503_;
            }
            4 => {
                if v_isShared_8509_ == 0 {
                    v___x_8511_ = v___x_8508_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8512_, 0, v_a_8506_);
                    v___x_8511_ = v_reuseFailAlloc_8512_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Handle_readToEnd___boxed(
    mut v_h_8514_: *mut LeanObject,
    mut v_a_8515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8516_: *mut LeanObject = core::ptr::null_mut();
    v_res_8516_ = l_IO_FS_Handle_readToEnd(v_h_8514_);
    lean_dec(v_h_8514_);
    return v_res_8516_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Handle_lines_read(
    mut v_h_8517_: *mut LeanObject,
    mut v_lines_8518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8524_: u8 = 0;
    let mut v___y_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8533_: u32 = 0;
    let mut v___x_8534_: u32 = 0;
    let mut v___x_8535_: u8 = 0;
    let mut v___x_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8541_: u32 = 0;
    let mut v___x_8542_: u32 = 0;
    let mut v___x_8543_: u8 = 0;
    let mut v___x_8544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: u32 = 0;
    let mut v_val_8558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8560_: u32 = 0;
    let mut v_val_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8562_: u32 = 0;
    let mut v___x_8563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8565_: u8 = 0;
    let mut v___x_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: u32 = 0;
    let mut v_val_8569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8571_: u32 = 0;
    let mut v_val_8572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: u32 = 0;
    let mut v___x_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8575_: u8 = 0;
    let mut v_a_8576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8579_: u8 = 0;
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8520_ = lean_io_prim_handle_get_line(v_h_8517_);
                if lean_obj_tag(v___x_8520_) == 0 {
                    v_a_8521_ = lean_ctor_get(v___x_8520_, 0);
                    v_isSharedCheck_8575_ = (!lean_is_exclusive(v___x_8520_)) as u8;
                    if v_isSharedCheck_8575_ == 0 {
                        v___x_8523_ = v___x_8520_;
                        v_isShared_8524_ = v_isSharedCheck_8575_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8521_);
                        lean_dec(v___x_8520_);
                        v___x_8523_ = lean_box(0);
                        v_isShared_8524_ = v_isSharedCheck_8575_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lines_8518_);
                    v_a_8576_ = lean_ctor_get(v___x_8520_, 0);
                    v_isSharedCheck_8583_ = (!lean_is_exclusive(v___x_8520_)) as u8;
                    if v_isSharedCheck_8583_ == 0 {
                        v___x_8578_ = v___x_8520_;
                        v_isShared_8579_ = v_isSharedCheck_8583_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8576_);
                        lean_dec(v___x_8520_);
                        v___x_8578_ = lean_box(0);
                        v_isShared_8579_ = v_isSharedCheck_8583_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8563_ = lean_string_utf8_byte_size(v_a_8521_);
                v___x_8564_ = lean_unsigned_to_nat(0);
                v___x_8565_ = lean_nat_dec_eq(v___x_8563_, v___x_8564_);
                if v___x_8565_ == 0 {
                    lean_inc(v_a_8521_);
                    v___x_8566_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_8566_, 0, v_a_8521_);
                    lean_ctor_set(v___x_8566_, 1, v___x_8564_);
                    lean_ctor_set(v___x_8566_, 2, v___x_8563_);
                    v___x_8567_ = l_String_Slice_Pos_prev_x3f(v___x_8566_, v___x_8563_);
                    if lean_obj_tag(v___x_8567_) == 0 {
                        lean_dec_ref_known(v___x_8566_, 3);
                        v___x_8568_ = 65;
                        v___y_8541_ = v___x_8568_;
                        state = 4;
                        continue;
                    } else {
                        v_val_8569_ = lean_ctor_get(v___x_8567_, 0);
                        lean_inc(v_val_8569_);
                        lean_dec_ref_known(v___x_8567_, 1);
                        v___x_8570_ = l_String_Slice_Pos_get_x3f(v___x_8566_, v_val_8569_);
                        lean_dec(v_val_8569_);
                        lean_dec_ref_known(v___x_8566_, 3);
                        if lean_obj_tag(v___x_8570_) == 0 {
                            v___x_8571_ = 65;
                            v___y_8541_ = v___x_8571_;
                            state = 4;
                            continue;
                        } else {
                            v_val_8572_ = lean_ctor_get(v___x_8570_, 0);
                            lean_inc(v_val_8572_);
                            lean_dec_ref_known(v___x_8570_, 1);
                            v___x_8573_ = lean_unbox_uint32(v_val_8572_);
                            lean_dec(v_val_8572_);
                            v___y_8541_ = v___x_8573_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_8523_);
                    lean_dec(v_a_8521_);
                    v___x_8574_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8574_, 0, v_lines_8518_);
                    return v___x_8574_;
                }
            }
            2 => {
                v___x_8527_ = lean_array_push(v_lines_8518_, v___y_8526_);
                v_lines_8518_ = v___x_8527_;
                state = 0;
                continue;
            }
            3 => {
                v___x_8534_ = 13;
                v___x_8535_ = lean_uint32_dec_eq(v___y_8533_, v___x_8534_);
                if v___x_8535_ == 0 {
                    lean_dec(v___y_8532_);
                    lean_dec(v___y_8530_);
                    v___y_8526_ = v___y_8531_;
                    state = 2;
                    continue;
                } else {
                    v___x_8536_ = lean_string_utf8_byte_size(v___y_8531_);
                    lean_inc(v___y_8530_);
                    lean_inc_ref(v___y_8531_);
                    v___x_8537_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_8537_, 0, v___y_8531_);
                    lean_ctor_set(v___x_8537_, 1, v___y_8530_);
                    lean_ctor_set(v___x_8537_, 2, v___x_8536_);
                    v___x_8538_ = l_String_Slice_Pos_prevn(v___x_8537_, v___x_8536_, v___y_8532_);
                    lean_dec_ref_known(v___x_8537_, 3);
                    v___x_8539_ = lean_string_utf8_extract(v___y_8531_, v___y_8530_, v___x_8538_);
                    lean_dec(v___x_8538_);
                    lean_dec(v___y_8530_);
                    lean_dec_ref(v___y_8531_);
                    v___y_8526_ = v___x_8539_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_8542_ = 10;
                v___x_8543_ = lean_uint32_dec_eq(v___y_8541_, v___x_8542_);
                if v___x_8543_ == 0 {
                    v___x_8544_ = lean_array_push(v_lines_8518_, v_a_8521_);
                    if v_isShared_8524_ == 0 {
                        lean_ctor_set(v___x_8523_, 0, v___x_8544_);
                        v___x_8546_ = v___x_8523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8547_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8547_, 0, v___x_8544_);
                        v___x_8546_ = v_reuseFailAlloc_8547_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8523_);
                    v___x_8548_ = lean_unsigned_to_nat(1);
                    v___x_8549_ = lean_unsigned_to_nat(0);
                    v___x_8550_ = lean_string_utf8_byte_size(v_a_8521_);
                    lean_inc(v_a_8521_);
                    v___x_8551_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_8551_, 0, v_a_8521_);
                    lean_ctor_set(v___x_8551_, 1, v___x_8549_);
                    lean_ctor_set(v___x_8551_, 2, v___x_8550_);
                    v___x_8552_ = l_String_Slice_Pos_prevn(v___x_8551_, v___x_8550_, v___x_8548_);
                    lean_dec_ref_known(v___x_8551_, 3);
                    v___x_8553_ = lean_string_utf8_extract(v_a_8521_, v___x_8549_, v___x_8552_);
                    lean_dec(v___x_8552_);
                    lean_dec(v_a_8521_);
                    v___x_8554_ = lean_string_utf8_byte_size(v___x_8553_);
                    lean_inc_ref(v___x_8553_);
                    v___x_8555_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_8555_, 0, v___x_8553_);
                    lean_ctor_set(v___x_8555_, 1, v___x_8549_);
                    lean_ctor_set(v___x_8555_, 2, v___x_8554_);
                    v___x_8556_ = l_String_Slice_Pos_prev_x3f(v___x_8555_, v___x_8554_);
                    if lean_obj_tag(v___x_8556_) == 0 {
                        lean_dec_ref_known(v___x_8555_, 3);
                        v___x_8557_ = 65;
                        v___y_8530_ = v___x_8549_;
                        v___y_8531_ = v___x_8553_;
                        v___y_8532_ = v___x_8548_;
                        v___y_8533_ = v___x_8557_;
                        state = 3;
                        continue;
                    } else {
                        v_val_8558_ = lean_ctor_get(v___x_8556_, 0);
                        lean_inc(v_val_8558_);
                        lean_dec_ref_known(v___x_8556_, 1);
                        v___x_8559_ = l_String_Slice_Pos_get_x3f(v___x_8555_, v_val_8558_);
                        lean_dec(v_val_8558_);
                        lean_dec_ref_known(v___x_8555_, 3);
                        if lean_obj_tag(v___x_8559_) == 0 {
                            v___x_8560_ = 65;
                            v___y_8530_ = v___x_8549_;
                            v___y_8531_ = v___x_8553_;
                            v___y_8532_ = v___x_8548_;
                            v___y_8533_ = v___x_8560_;
                            state = 3;
                            continue;
                        } else {
                            v_val_8561_ = lean_ctor_get(v___x_8559_, 0);
                            lean_inc(v_val_8561_);
                            lean_dec_ref_known(v___x_8559_, 1);
                            v___x_8562_ = lean_unbox_uint32(v_val_8561_);
                            lean_dec(v_val_8561_);
                            v___y_8530_ = v___x_8549_;
                            v___y_8531_ = v___x_8553_;
                            v___y_8532_ = v___x_8548_;
                            v___y_8533_ = v___x_8562_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_8546_;
            }
            6 => {
                if v_isShared_8579_ == 0 {
                    v___x_8581_ = v___x_8578_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8582_, 0, v_a_8576_);
                    v___x_8581_ = v_reuseFailAlloc_8582_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(
    mut v_h_8584_: *mut LeanObject,
    mut v_lines_8585_: *mut LeanObject,
    mut v_a_8586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8587_: *mut LeanObject = core::ptr::null_mut();
    v_res_8587_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_8584_, v_lines_8585_);
    lean_dec(v_h_8584_);
    return v_res_8587_;
}
pub unsafe fn l_IO_FS_Handle_lines(mut v_h_8590_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8593_: *mut LeanObject = core::ptr::null_mut();
    v___x_8592_ = l_IO_FS_Handle_lines___closed__0;
    v___x_8593_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_8590_, v___x_8592_);
    return v___x_8593_;
}
pub unsafe fn l_IO_FS_Handle_lines___boxed(
    mut v_h_8594_: *mut LeanObject,
    mut v_a_8595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8596_: *mut LeanObject = core::ptr::null_mut();
    v_res_8596_ = l_IO_FS_Handle_lines(v_h_8594_);
    lean_dec(v_h_8594_);
    return v_res_8596_;
}
pub unsafe fn l_IO_FS_lines(mut v_fname_8597_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8599_: u8 = 0;
    let mut v___x_8600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8606_: u8 = 0;
    let mut v___x_8608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8599_ = 0;
                v___x_8600_ = lean_io_prim_handle_mk(v_fname_8597_, v___x_8599_);
                if lean_obj_tag(v___x_8600_) == 0 {
                    v_a_8601_ = lean_ctor_get(v___x_8600_, 0);
                    lean_inc(v_a_8601_);
                    lean_dec_ref_known(v___x_8600_, 1);
                    v___x_8602_ = l_IO_FS_Handle_lines(v_a_8601_);
                    lean_dec(v_a_8601_);
                    return v___x_8602_;
                } else {
                    v_a_8603_ = lean_ctor_get(v___x_8600_, 0);
                    v_isSharedCheck_8610_ = (!lean_is_exclusive(v___x_8600_)) as u8;
                    if v_isSharedCheck_8610_ == 0 {
                        v___x_8605_ = v___x_8600_;
                        v_isShared_8606_ = v_isSharedCheck_8610_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8603_);
                        lean_dec(v___x_8600_);
                        v___x_8605_ = lean_box(0);
                        v_isShared_8606_ = v_isSharedCheck_8610_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8606_ == 0 {
                    v___x_8608_ = v___x_8605_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8609_, 0, v_a_8603_);
                    v___x_8608_ = v_reuseFailAlloc_8609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_lines___boxed(
    mut v_fname_8611_: *mut LeanObject,
    mut v_a_8612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8613_: *mut LeanObject = core::ptr::null_mut();
    v_res_8613_ = l_IO_FS_lines(v_fname_8611_);
    lean_dec_ref(v_fname_8611_);
    return v_res_8613_;
}
pub unsafe fn l_IO_FS_writeBinFile(
    mut v_fname_8614_: *mut LeanObject,
    mut v_content_8615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8617_: u8 = 0;
    let mut v___x_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8624_: u8 = 0;
    let mut v___x_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8617_ = 1;
                v___x_8618_ = lean_io_prim_handle_mk(v_fname_8614_, v___x_8617_);
                if lean_obj_tag(v___x_8618_) == 0 {
                    v_a_8619_ = lean_ctor_get(v___x_8618_, 0);
                    lean_inc(v_a_8619_);
                    lean_dec_ref_known(v___x_8618_, 1);
                    v___x_8620_ = lean_io_prim_handle_write(v_a_8619_, v_content_8615_);
                    lean_dec(v_a_8619_);
                    return v___x_8620_;
                } else {
                    v_a_8621_ = lean_ctor_get(v___x_8618_, 0);
                    v_isSharedCheck_8628_ = (!lean_is_exclusive(v___x_8618_)) as u8;
                    if v_isSharedCheck_8628_ == 0 {
                        v___x_8623_ = v___x_8618_;
                        v_isShared_8624_ = v_isSharedCheck_8628_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8621_);
                        lean_dec(v___x_8618_);
                        v___x_8623_ = lean_box(0);
                        v_isShared_8624_ = v_isSharedCheck_8628_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8624_ == 0 {
                    v___x_8626_ = v___x_8623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8627_, 0, v_a_8621_);
                    v___x_8626_ = v_reuseFailAlloc_8627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_writeBinFile___boxed(
    mut v_fname_8629_: *mut LeanObject,
    mut v_content_8630_: *mut LeanObject,
    mut v_a_8631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8632_: *mut LeanObject = core::ptr::null_mut();
    v_res_8632_ = l_IO_FS_writeBinFile(v_fname_8629_, v_content_8630_);
    lean_dec_ref(v_content_8630_);
    lean_dec_ref(v_fname_8629_);
    return v_res_8632_;
}
pub unsafe fn l_IO_FS_writeFile(
    mut v_fname_8633_: *mut LeanObject,
    mut v_content_8634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8636_: u8 = 0;
    let mut v___x_8637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8643_: u8 = 0;
    let mut v___x_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8636_ = 1;
                v___x_8637_ = lean_io_prim_handle_mk(v_fname_8633_, v___x_8636_);
                if lean_obj_tag(v___x_8637_) == 0 {
                    v_a_8638_ = lean_ctor_get(v___x_8637_, 0);
                    lean_inc(v_a_8638_);
                    lean_dec_ref_known(v___x_8637_, 1);
                    v___x_8639_ = lean_io_prim_handle_put_str(v_a_8638_, v_content_8634_);
                    lean_dec(v_a_8638_);
                    return v___x_8639_;
                } else {
                    v_a_8640_ = lean_ctor_get(v___x_8637_, 0);
                    v_isSharedCheck_8647_ = (!lean_is_exclusive(v___x_8637_)) as u8;
                    if v_isSharedCheck_8647_ == 0 {
                        v___x_8642_ = v___x_8637_;
                        v_isShared_8643_ = v_isSharedCheck_8647_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8640_);
                        lean_dec(v___x_8637_);
                        v___x_8642_ = lean_box(0);
                        v_isShared_8643_ = v_isSharedCheck_8647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8643_ == 0 {
                    v___x_8645_ = v___x_8642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8646_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8646_, 0, v_a_8640_);
                    v___x_8645_ = v_reuseFailAlloc_8646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_writeFile___boxed(
    mut v_fname_8648_: *mut LeanObject,
    mut v_content_8649_: *mut LeanObject,
    mut v_a_8650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8651_: *mut LeanObject = core::ptr::null_mut();
    v_res_8651_ = l_IO_FS_writeFile(v_fname_8648_, v_content_8649_);
    lean_dec_ref(v_content_8649_);
    lean_dec_ref(v_fname_8648_);
    return v_res_8651_;
}
pub unsafe fn l_IO_FS_Stream_putStrLn(
    mut v_strm_8652_: *mut LeanObject,
    mut v_s_8653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_putStr_8655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8656_: u32 = 0;
    let mut v___x_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    v_putStr_8655_ = lean_ctor_get(v_strm_8652_, 4);
    lean_inc_ref(v_putStr_8655_);
    lean_dec_ref(v_strm_8652_);
    v___x_8656_ = 10;
    v___x_8657_ = lean_string_push(v_s_8653_, v___x_8656_);
    v___x_8658_ = lean_apply_2(v_putStr_8655_, v___x_8657_, lean_box(0));
    return v___x_8658_;
}
pub unsafe fn l_IO_FS_Stream_putStrLn___boxed(
    mut v_strm_8659_: *mut LeanObject,
    mut v_s_8660_: *mut LeanObject,
    mut v_a_8661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8662_: *mut LeanObject = core::ptr::null_mut();
    v_res_8662_ = l_IO_FS_Stream_putStrLn(v_strm_8659_, v_s_8660_);
    return v_res_8662_;
}
pub unsafe fn l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(
    mut v_a_8663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8664_: *mut LeanObject = core::ptr::null_mut();
    v___x_8664_ = lean_nat_to_int(v_a_8663_);
    return v___x_8664_;
}
pub unsafe fn _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8679_: *mut LeanObject = core::ptr::null_mut();
    v___x_8678_ = lean_unsigned_to_nat(8);
    v___x_8679_ = lean_nat_to_int(v___x_8678_);
    return v___x_8679_;
}
pub unsafe fn _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_8689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8690_: *mut LeanObject = core::ptr::null_mut();
    v___x_8689_ = lean_unsigned_to_nat(12);
    v___x_8690_ = lean_nat_to_int(v___x_8689_);
    return v___x_8690_;
}
pub unsafe fn _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_8692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8693_: *mut LeanObject = core::ptr::null_mut();
    v___x_8692_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__0;
    v___x_8693_ = lean_string_length(v___x_8692_);
    return v___x_8693_;
}
pub unsafe fn _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_8694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8695_: *mut LeanObject = core::ptr::null_mut();
    v___x_8694_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once),
        _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16,
    );
    v___x_8695_ = lean_nat_to_int(v___x_8694_);
    return v___x_8695_;
}
pub unsafe fn l_IO_FS_instReprDirEntry_repr___redArg(
    mut v_x_8700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8705_: u8 = 0;
    let mut v___x_8706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8717_: u8 = 0;
    let mut v___x_8718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_8701_ = lean_ctor_get(v_x_8700_, 0);
                v_fileName_8702_ = lean_ctor_get(v_x_8700_, 1);
                v_isSharedCheck_8741_ = (!lean_is_exclusive(v_x_8700_)) as u8;
                if v_isSharedCheck_8741_ == 0 {
                    v___x_8704_ = v_x_8700_;
                    v_isShared_8705_ = v_isSharedCheck_8741_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fileName_8702_);
                    lean_inc(v_root_8701_);
                    lean_dec(v_x_8700_);
                    v___x_8704_ = lean_box(0);
                    v_isShared_8705_ = v_isSharedCheck_8741_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8706_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
                v___x_8707_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__6;
                v___x_8708_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once
                    ),
                    _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7,
                );
                v___x_8709_ = lean_unsigned_to_nat(0);
                v___x_8710_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__9;
                v___x_8711_ = l_String_quote(v_root_8701_);
                v___x_8712_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_8712_, 0, v___x_8711_);
                if v_isShared_8705_ == 0 {
                    lean_ctor_set_tag(v___x_8704_, 5);
                    lean_ctor_set(v___x_8704_, 1, v___x_8712_);
                    lean_ctor_set(v___x_8704_, 0, v___x_8710_);
                    v___x_8714_ = v___x_8704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8740_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8740_, 0, v___x_8710_);
                    lean_ctor_set(v_reuseFailAlloc_8740_, 1, v___x_8712_);
                    v___x_8714_ = v_reuseFailAlloc_8740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8715_ = l_Repr_addAppParen(v___x_8714_, v___x_8709_);
                v___x_8716_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8716_, 0, v___x_8708_);
                lean_ctor_set(v___x_8716_, 1, v___x_8715_);
                v___x_8717_ = 0;
                v___x_8718_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8718_, 0, v___x_8716_);
                lean_ctor_set_uint8(
                    v___x_8718_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8717_,
                );
                v___x_8719_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8719_, 0, v___x_8707_);
                lean_ctor_set(v___x_8719_, 1, v___x_8718_);
                v___x_8720_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
                v___x_8721_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8721_, 0, v___x_8719_);
                lean_ctor_set(v___x_8721_, 1, v___x_8720_);
                v___x_8722_ = lean_box(1);
                v___x_8723_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8723_, 0, v___x_8721_);
                lean_ctor_set(v___x_8723_, 1, v___x_8722_);
                v___x_8724_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__13;
                v___x_8725_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8725_, 0, v___x_8723_);
                lean_ctor_set(v___x_8725_, 1, v___x_8724_);
                v___x_8726_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8726_, 0, v___x_8725_);
                lean_ctor_set(v___x_8726_, 1, v___x_8706_);
                v___x_8727_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__14),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once
                    ),
                    _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14,
                );
                v___x_8728_ = l_String_quote(v_fileName_8702_);
                v___x_8729_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_8729_, 0, v___x_8728_);
                v___x_8730_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8730_, 0, v___x_8727_);
                lean_ctor_set(v___x_8730_, 1, v___x_8729_);
                v___x_8731_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8731_, 0, v___x_8730_);
                lean_ctor_set_uint8(
                    v___x_8731_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8717_,
                );
                v___x_8732_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8732_, 0, v___x_8726_);
                lean_ctor_set(v___x_8732_, 1, v___x_8731_);
                v___x_8733_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__17),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once
                    ),
                    _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17,
                );
                v___x_8734_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
                v___x_8735_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8735_, 0, v___x_8734_);
                lean_ctor_set(v___x_8735_, 1, v___x_8732_);
                v___x_8736_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
                v___x_8737_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8737_, 0, v___x_8735_);
                lean_ctor_set(v___x_8737_, 1, v___x_8736_);
                v___x_8738_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8738_, 0, v___x_8733_);
                lean_ctor_set(v___x_8738_, 1, v___x_8737_);
                v___x_8739_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8739_, 0, v___x_8738_);
                lean_ctor_set_uint8(
                    v___x_8739_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8717_,
                );
                return v___x_8739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_instReprDirEntry_repr(
    mut v_x_8742_: *mut LeanObject,
    mut v_prec_8743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    v___x_8744_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_8742_);
    return v___x_8744_;
}
pub unsafe fn l_IO_FS_instReprDirEntry_repr___boxed(
    mut v_x_8745_: *mut LeanObject,
    mut v_prec_8746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8747_: *mut LeanObject = core::ptr::null_mut();
    v_res_8747_ = l_IO_FS_instReprDirEntry_repr(v_x_8745_, v_prec_8746_);
    lean_dec(v_prec_8746_);
    return v_res_8747_;
}
pub unsafe fn l_IO_FS_DirEntry_path(mut v_entry_8750_: *mut LeanObject) -> *mut LeanObject {
    let mut v_root_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    v_root_8751_ = lean_ctor_get(v_entry_8750_, 0);
    lean_inc_ref(v_root_8751_);
    v_fileName_8752_ = lean_ctor_get(v_entry_8750_, 1);
    lean_inc_ref(v_fileName_8752_);
    lean_dec_ref(v_entry_8750_);
    v___x_8753_ = l_System_FilePath_join(v_root_8751_, v_fileName_8752_);
    return v___x_8753_;
}
pub unsafe fn l_IO_FS_FileType_ctorIdx(mut v_x_8754_: u8) -> *mut LeanObject {
    match v_x_8754_ {
        0 => {
            let mut v___x_8755_: *mut LeanObject = core::ptr::null_mut();
            v___x_8755_ = lean_unsigned_to_nat(0);
            return v___x_8755_;
        }
        1 => {
            let mut v___x_8756_: *mut LeanObject = core::ptr::null_mut();
            v___x_8756_ = lean_unsigned_to_nat(1);
            return v___x_8756_;
        }
        2 => {
            let mut v___x_8757_: *mut LeanObject = core::ptr::null_mut();
            v___x_8757_ = lean_unsigned_to_nat(2);
            return v___x_8757_;
        }
        _ => {
            let mut v___x_8758_: *mut LeanObject = core::ptr::null_mut();
            v___x_8758_ = lean_unsigned_to_nat(3);
            return v___x_8758_;
        }
    }
}
pub unsafe fn l_IO_FS_FileType_ctorIdx___boxed(mut v_x_8759_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_8760_: u8 = 0;
    let mut v_res_8761_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_8760_ = (lean_unbox(v_x_8759_) as u8);
    v_res_8761_ = l_IO_FS_FileType_ctorIdx(v_x_boxed_8760_);
    return v_res_8761_;
}
pub unsafe fn l_IO_FS_FileType_toCtorIdx(mut v_x_8762_: u8) -> *mut LeanObject {
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    v___x_8763_ = l_IO_FS_FileType_ctorIdx(v_x_8762_);
    return v___x_8763_;
}
pub unsafe fn l_IO_FS_FileType_toCtorIdx___boxed(
    mut v_x_8764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_8765_: u8 = 0;
    let mut v_res_8766_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_8765_ = (lean_unbox(v_x_8764_) as u8);
    v_res_8766_ = l_IO_FS_FileType_toCtorIdx(v_x_4__boxed_8765_);
    return v_res_8766_;
}
pub unsafe fn l_IO_FS_FileType_ctorElim___redArg(
    mut v_k_8767_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_8767_);
    return v_k_8767_;
}
pub unsafe fn l_IO_FS_FileType_ctorElim___redArg___boxed(
    mut v_k_8768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8769_: *mut LeanObject = core::ptr::null_mut();
    v_res_8769_ = l_IO_FS_FileType_ctorElim___redArg(v_k_8768_);
    lean_dec(v_k_8768_);
    return v_res_8769_;
}
pub unsafe fn l_IO_FS_FileType_ctorElim(
    mut v_motive_8770_: *mut LeanObject,
    mut v_ctorIdx_8771_: *mut LeanObject,
    mut v_t_8772_: u8,
    mut v_h_8773_: *mut LeanObject,
    mut v_k_8774_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_8774_);
    return v_k_8774_;
}
pub unsafe fn l_IO_FS_FileType_ctorElim___boxed(
    mut v_motive_8775_: *mut LeanObject,
    mut v_ctorIdx_8776_: *mut LeanObject,
    mut v_t_8777_: *mut LeanObject,
    mut v_h_8778_: *mut LeanObject,
    mut v_k_8779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8780_: u8 = 0;
    let mut v_res_8781_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8780_ = (lean_unbox(v_t_8777_) as u8);
    v_res_8781_ = l_IO_FS_FileType_ctorElim(
        v_motive_8775_,
        v_ctorIdx_8776_,
        v_t_boxed_8780_,
        v_h_8778_,
        v_k_8779_,
    );
    lean_dec(v_k_8779_);
    lean_dec(v_ctorIdx_8776_);
    return v_res_8781_;
}
pub unsafe fn l_IO_FS_FileType_dir_elim___redArg(
    mut v_dir_8782_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_dir_8782_);
    return v_dir_8782_;
}
pub unsafe fn l_IO_FS_FileType_dir_elim___redArg___boxed(
    mut v_dir_8783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8784_: *mut LeanObject = core::ptr::null_mut();
    v_res_8784_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_8783_);
    lean_dec(v_dir_8783_);
    return v_res_8784_;
}
pub unsafe fn l_IO_FS_FileType_dir_elim(
    mut v_motive_8785_: *mut LeanObject,
    mut v_t_8786_: u8,
    mut v_h_8787_: *mut LeanObject,
    mut v_dir_8788_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_dir_8788_);
    return v_dir_8788_;
}
pub unsafe fn l_IO_FS_FileType_dir_elim___boxed(
    mut v_motive_8789_: *mut LeanObject,
    mut v_t_8790_: *mut LeanObject,
    mut v_h_8791_: *mut LeanObject,
    mut v_dir_8792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8793_: u8 = 0;
    let mut v_res_8794_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8793_ = (lean_unbox(v_t_8790_) as u8);
    v_res_8794_ =
        l_IO_FS_FileType_dir_elim(v_motive_8789_, v_t_boxed_8793_, v_h_8791_, v_dir_8792_);
    lean_dec(v_dir_8792_);
    return v_res_8794_;
}
pub unsafe fn l_IO_FS_FileType_file_elim___redArg(
    mut v_file_8795_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_file_8795_);
    return v_file_8795_;
}
pub unsafe fn l_IO_FS_FileType_file_elim___redArg___boxed(
    mut v_file_8796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8797_: *mut LeanObject = core::ptr::null_mut();
    v_res_8797_ = l_IO_FS_FileType_file_elim___redArg(v_file_8796_);
    lean_dec(v_file_8796_);
    return v_res_8797_;
}
pub unsafe fn l_IO_FS_FileType_file_elim(
    mut v_motive_8798_: *mut LeanObject,
    mut v_t_8799_: u8,
    mut v_h_8800_: *mut LeanObject,
    mut v_file_8801_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_file_8801_);
    return v_file_8801_;
}
pub unsafe fn l_IO_FS_FileType_file_elim___boxed(
    mut v_motive_8802_: *mut LeanObject,
    mut v_t_8803_: *mut LeanObject,
    mut v_h_8804_: *mut LeanObject,
    mut v_file_8805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8806_: u8 = 0;
    let mut v_res_8807_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8806_ = (lean_unbox(v_t_8803_) as u8);
    v_res_8807_ =
        l_IO_FS_FileType_file_elim(v_motive_8802_, v_t_boxed_8806_, v_h_8804_, v_file_8805_);
    lean_dec(v_file_8805_);
    return v_res_8807_;
}
pub unsafe fn l_IO_FS_FileType_symlink_elim___redArg(
    mut v_symlink_8808_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_symlink_8808_);
    return v_symlink_8808_;
}
pub unsafe fn l_IO_FS_FileType_symlink_elim___redArg___boxed(
    mut v_symlink_8809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8810_: *mut LeanObject = core::ptr::null_mut();
    v_res_8810_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_8809_);
    lean_dec(v_symlink_8809_);
    return v_res_8810_;
}
pub unsafe fn l_IO_FS_FileType_symlink_elim(
    mut v_motive_8811_: *mut LeanObject,
    mut v_t_8812_: u8,
    mut v_h_8813_: *mut LeanObject,
    mut v_symlink_8814_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_symlink_8814_);
    return v_symlink_8814_;
}
pub unsafe fn l_IO_FS_FileType_symlink_elim___boxed(
    mut v_motive_8815_: *mut LeanObject,
    mut v_t_8816_: *mut LeanObject,
    mut v_h_8817_: *mut LeanObject,
    mut v_symlink_8818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8819_: u8 = 0;
    let mut v_res_8820_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8819_ = (lean_unbox(v_t_8816_) as u8);
    v_res_8820_ =
        l_IO_FS_FileType_symlink_elim(v_motive_8815_, v_t_boxed_8819_, v_h_8817_, v_symlink_8818_);
    lean_dec(v_symlink_8818_);
    return v_res_8820_;
}
pub unsafe fn l_IO_FS_FileType_other_elim___redArg(
    mut v_other_8821_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_other_8821_);
    return v_other_8821_;
}
pub unsafe fn l_IO_FS_FileType_other_elim___redArg___boxed(
    mut v_other_8822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8823_: *mut LeanObject = core::ptr::null_mut();
    v_res_8823_ = l_IO_FS_FileType_other_elim___redArg(v_other_8822_);
    lean_dec(v_other_8822_);
    return v_res_8823_;
}
pub unsafe fn l_IO_FS_FileType_other_elim(
    mut v_motive_8824_: *mut LeanObject,
    mut v_t_8825_: u8,
    mut v_h_8826_: *mut LeanObject,
    mut v_other_8827_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_other_8827_);
    return v_other_8827_;
}
pub unsafe fn l_IO_FS_FileType_other_elim___boxed(
    mut v_motive_8828_: *mut LeanObject,
    mut v_t_8829_: *mut LeanObject,
    mut v_h_8830_: *mut LeanObject,
    mut v_other_8831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_8832_: u8 = 0;
    let mut v_res_8833_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_8832_ = (lean_unbox(v_t_8829_) as u8);
    v_res_8833_ =
        l_IO_FS_FileType_other_elim(v_motive_8828_, v_t_boxed_8832_, v_h_8830_, v_other_8831_);
    lean_dec(v_other_8831_);
    return v_res_8833_;
}
pub unsafe fn l_IO_FS_instReprFileType_repr(
    mut v_x_8846_: u8,
    mut v_prec_8847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8852_: u8 = 0;
    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8859_: u8 = 0;
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8866_: u8 = 0;
    let mut v___x_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: u8 = 0;
    let mut v___x_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: u8 = 0;
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8881_: u8 = 0;
    let mut v___x_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8885_: u8 = 0;
    let mut v___x_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8889_: u8 = 0;
    let mut v___x_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_8846_ {
                0 => {
                    v___x_8876_ = lean_unsigned_to_nat(1024);
                    v___x_8877_ = lean_nat_dec_le(v___x_8876_, v_prec_8847_);
                    if v___x_8877_ == 0 {
                        v___x_8878_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_8849_ = v___x_8878_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8879_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_8849_ = v___x_8879_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_8880_ = lean_unsigned_to_nat(1024);
                    v___x_8881_ = lean_nat_dec_le(v___x_8880_, v_prec_8847_);
                    if v___x_8881_ == 0 {
                        v___x_8882_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_8856_ = v___x_8882_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8883_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_8856_ = v___x_8883_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_8884_ = lean_unsigned_to_nat(1024);
                    v___x_8885_ = lean_nat_dec_le(v___x_8884_, v_prec_8847_);
                    if v___x_8885_ == 0 {
                        v___x_8886_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_8863_ = v___x_8886_;
                        state = 3;
                        continue;
                    } else {
                        v___x_8887_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_8863_ = v___x_8887_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_8888_ = lean_unsigned_to_nat(1024);
                    v___x_8889_ = lean_nat_dec_le(v___x_8888_, v_prec_8847_);
                    if v___x_8889_ == 0 {
                        v___x_8890_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__6_once),
                            _init_l_IO_instReprTaskState_repr___closed__6,
                        );
                        v___y_8870_ = v___x_8890_;
                        state = 4;
                        continue;
                    } else {
                        v___x_8891_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7),
                            core::ptr::addr_of_mut!(l_IO_instReprTaskState_repr___closed__7_once),
                            _init_l_IO_instReprTaskState_repr___closed__7,
                        );
                        v___y_8870_ = v___x_8891_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_8850_ = l_IO_FS_instReprFileType_repr___closed__1;
                lean_inc(v___y_8849_);
                v___x_8851_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8851_, 0, v___y_8849_);
                lean_ctor_set(v___x_8851_, 1, v___x_8850_);
                v___x_8852_ = 0;
                v___x_8853_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8853_, 0, v___x_8851_);
                lean_ctor_set_uint8(
                    v___x_8853_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8852_,
                );
                v___x_8854_ = l_Repr_addAppParen(v___x_8853_, v_prec_8847_);
                return v___x_8854_;
            }
            2 => {
                v___x_8857_ = l_IO_FS_instReprFileType_repr___closed__3;
                lean_inc(v___y_8856_);
                v___x_8858_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8858_, 0, v___y_8856_);
                lean_ctor_set(v___x_8858_, 1, v___x_8857_);
                v___x_8859_ = 0;
                v___x_8860_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8860_, 0, v___x_8858_);
                lean_ctor_set_uint8(
                    v___x_8860_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8859_,
                );
                v___x_8861_ = l_Repr_addAppParen(v___x_8860_, v_prec_8847_);
                return v___x_8861_;
            }
            3 => {
                v___x_8864_ = l_IO_FS_instReprFileType_repr___closed__5;
                lean_inc(v___y_8863_);
                v___x_8865_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8865_, 0, v___y_8863_);
                lean_ctor_set(v___x_8865_, 1, v___x_8864_);
                v___x_8866_ = 0;
                v___x_8867_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8867_, 0, v___x_8865_);
                lean_ctor_set_uint8(
                    v___x_8867_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8866_,
                );
                v___x_8868_ = l_Repr_addAppParen(v___x_8867_, v_prec_8847_);
                return v___x_8868_;
            }
            4 => {
                v___x_8871_ = l_IO_FS_instReprFileType_repr___closed__7;
                lean_inc(v___y_8870_);
                v___x_8872_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8872_, 0, v___y_8870_);
                lean_ctor_set(v___x_8872_, 1, v___x_8871_);
                v___x_8873_ = 0;
                v___x_8874_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8874_, 0, v___x_8872_);
                lean_ctor_set_uint8(
                    v___x_8874_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8873_,
                );
                v___x_8875_ = l_Repr_addAppParen(v___x_8874_, v_prec_8847_);
                return v___x_8875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_instReprFileType_repr___boxed(
    mut v_x_8892_: *mut LeanObject,
    mut v_prec_8893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_229__boxed_8894_: u8 = 0;
    let mut v_res_8895_: *mut LeanObject = core::ptr::null_mut();
    v_x_229__boxed_8894_ = (lean_unbox(v_x_8892_) as u8);
    v_res_8895_ = l_IO_FS_instReprFileType_repr(v_x_229__boxed_8894_, v_prec_8893_);
    lean_dec(v_prec_8893_);
    return v_res_8895_;
}
pub unsafe fn l_IO_FS_instBEqFileType_beq(mut v_x_8898_: u8, mut v_y_8899_: u8) -> u8 {
    let mut v___x_8900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8902_: u8 = 0;
    v___x_8900_ = l_IO_FS_FileType_ctorIdx(v_x_8898_);
    v___x_8901_ = l_IO_FS_FileType_ctorIdx(v_y_8899_);
    v___x_8902_ = lean_nat_dec_eq(v___x_8900_, v___x_8901_);
    lean_dec(v___x_8901_);
    lean_dec(v___x_8900_);
    return v___x_8902_;
}
pub unsafe fn l_IO_FS_instBEqFileType_beq___boxed(
    mut v_x_8903_: *mut LeanObject,
    mut v_y_8904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_8905_: u8 = 0;
    let mut v_y_18__boxed_8906_: u8 = 0;
    let mut v_res_8907_: u8 = 0;
    let mut v_r_8908_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_8905_ = (lean_unbox(v_x_8903_) as u8);
    v_y_18__boxed_8906_ = (lean_unbox(v_y_8904_) as u8);
    v_res_8907_ = l_IO_FS_instBEqFileType_beq(v_x_17__boxed_8905_, v_y_18__boxed_8906_);
    v_r_8908_ = lean_box((v_res_8907_) as usize);
    return v_r_8908_;
}
pub unsafe fn _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_8920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8921_: *mut LeanObject = core::ptr::null_mut();
    v___x_8920_ = lean_unsigned_to_nat(7);
    v___x_8921_ = lean_nat_to_int(v___x_8920_);
    return v___x_8921_;
}
pub unsafe fn _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_8925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8926_: *mut LeanObject = core::ptr::null_mut();
    v___x_8925_ = lean_unsigned_to_nat(0);
    v___x_8926_ = lean_nat_to_int(v___x_8925_);
    return v___x_8926_;
}
pub unsafe fn l_IO_FS_instReprSystemTime_repr___redArg(
    mut v_x_8927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sec_8928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsec_8929_: u32 = 0;
    let mut v___x_8930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8936_: u8 = 0;
    let mut v___x_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: u8 = 0;
    let mut v___x_8963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sec_8928_ = lean_ctor_get(v_x_8927_, 0);
                v_nsec_8929_ = lean_ctor_get_uint32(
                    v_x_8927_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_8930_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
                v___x_8931_ = l_IO_FS_instReprSystemTime_repr___redArg___closed__3;
                v___x_8932_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprSystemTime_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once
                    ),
                    _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4,
                );
                v___x_8960_ = lean_unsigned_to_nat(0);
                v___x_8961_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprSystemTime_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once
                    ),
                    _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7,
                );
                v___x_8962_ = lean_int_dec_lt(v_sec_8928_, v___x_8961_);
                if v___x_8962_ == 0 {
                    v___x_8963_ = l_Int_repr(v_sec_8928_);
                    v___x_8964_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_8964_, 0, v___x_8963_);
                    v___y_8934_ = v___x_8964_;
                    state = 1;
                    continue;
                } else {
                    v___x_8965_ = l_Int_repr(v_sec_8928_);
                    v___x_8966_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_8966_, 0, v___x_8965_);
                    v___x_8967_ = l_Repr_addAppParen(v___x_8966_, v___x_8960_);
                    v___y_8934_ = v___x_8967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8935_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8935_, 0, v___x_8932_);
                lean_ctor_set(v___x_8935_, 1, v___y_8934_);
                v___x_8936_ = 0;
                v___x_8937_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8937_, 0, v___x_8935_);
                lean_ctor_set_uint8(
                    v___x_8937_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8936_,
                );
                v___x_8938_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8938_, 0, v___x_8931_);
                lean_ctor_set(v___x_8938_, 1, v___x_8937_);
                v___x_8939_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
                v___x_8940_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8940_, 0, v___x_8938_);
                lean_ctor_set(v___x_8940_, 1, v___x_8939_);
                v___x_8941_ = lean_box(1);
                v___x_8942_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8942_, 0, v___x_8940_);
                lean_ctor_set(v___x_8942_, 1, v___x_8941_);
                v___x_8943_ = l_IO_FS_instReprSystemTime_repr___redArg___closed__6;
                v___x_8944_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8944_, 0, v___x_8942_);
                lean_ctor_set(v___x_8944_, 1, v___x_8943_);
                v___x_8945_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8945_, 0, v___x_8944_);
                lean_ctor_set(v___x_8945_, 1, v___x_8930_);
                v___x_8946_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once
                    ),
                    _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7,
                );
                v___x_8947_ = lean_uint32_to_nat(v_nsec_8929_);
                v___x_8948_ = l_Nat_reprFast(v___x_8947_);
                v___x_8949_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_8949_, 0, v___x_8948_);
                v___x_8950_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8950_, 0, v___x_8946_);
                lean_ctor_set(v___x_8950_, 1, v___x_8949_);
                v___x_8951_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8951_, 0, v___x_8950_);
                lean_ctor_set_uint8(
                    v___x_8951_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8936_,
                );
                v___x_8952_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8952_, 0, v___x_8945_);
                lean_ctor_set(v___x_8952_, 1, v___x_8951_);
                v___x_8953_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__17),
                    core::ptr::addr_of_mut!(
                        l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once
                    ),
                    _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17,
                );
                v___x_8954_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
                v___x_8955_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8955_, 0, v___x_8954_);
                lean_ctor_set(v___x_8955_, 1, v___x_8952_);
                v___x_8956_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
                v___x_8957_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_8957_, 0, v___x_8955_);
                lean_ctor_set(v___x_8957_, 1, v___x_8956_);
                v___x_8958_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8958_, 0, v___x_8953_);
                lean_ctor_set(v___x_8958_, 1, v___x_8957_);
                v___x_8959_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_8959_, 0, v___x_8958_);
                lean_ctor_set_uint8(
                    v___x_8959_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8936_,
                );
                return v___x_8959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_instReprSystemTime_repr___redArg___boxed(
    mut v_x_8968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8969_: *mut LeanObject = core::ptr::null_mut();
    v_res_8969_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_8968_);
    lean_dec_ref(v_x_8968_);
    return v_res_8969_;
}
pub unsafe fn l_IO_FS_instReprSystemTime_repr(
    mut v_x_8970_: *mut LeanObject,
    mut v_prec_8971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8972_: *mut LeanObject = core::ptr::null_mut();
    v___x_8972_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_8970_);
    return v___x_8972_;
}
pub unsafe fn l_IO_FS_instReprSystemTime_repr___boxed(
    mut v_x_8973_: *mut LeanObject,
    mut v_prec_8974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8975_: *mut LeanObject = core::ptr::null_mut();
    v_res_8975_ = l_IO_FS_instReprSystemTime_repr(v_x_8973_, v_prec_8974_);
    lean_dec(v_prec_8974_);
    lean_dec_ref(v_x_8973_);
    return v_res_8975_;
}
pub unsafe fn l_IO_FS_instBEqSystemTime_beq(
    mut v_x_8978_: *mut LeanObject,
    mut v_x_8979_: *mut LeanObject,
) -> u8 {
    let mut v_sec_8980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsec_8981_: u32 = 0;
    let mut v_sec_8982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsec_8983_: u32 = 0;
    let mut v___x_8984_: u8 = 0;
    v_sec_8980_ = lean_ctor_get(v_x_8978_, 0);
    v_nsec_8981_ = lean_ctor_get_uint32(
        v_x_8978_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_sec_8982_ = lean_ctor_get(v_x_8979_, 0);
    v_nsec_8983_ = lean_ctor_get_uint32(
        v_x_8979_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_8984_ = lean_int_dec_eq(v_sec_8980_, v_sec_8982_);
    if v___x_8984_ == 0 {
        return v___x_8984_;
    } else {
        let mut v___x_8985_: u8 = 0;
        v___x_8985_ = lean_uint32_dec_eq(v_nsec_8981_, v_nsec_8983_);
        return v___x_8985_;
    }
}
pub unsafe fn l_IO_FS_instBEqSystemTime_beq___boxed(
    mut v_x_8986_: *mut LeanObject,
    mut v_x_8987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8988_: u8 = 0;
    let mut v_r_8989_: *mut LeanObject = core::ptr::null_mut();
    v_res_8988_ = l_IO_FS_instBEqSystemTime_beq(v_x_8986_, v_x_8987_);
    lean_dec_ref(v_x_8987_);
    lean_dec_ref(v_x_8986_);
    v_r_8989_ = lean_box((v_res_8988_) as usize);
    return v_r_8989_;
}
pub unsafe fn l_IO_FS_instOrdSystemTime_ord(
    mut v_x_8992_: *mut LeanObject,
    mut v_x_8993_: *mut LeanObject,
) -> u8 {
    let mut v_sec_8994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsec_8995_: u32 = 0;
    let mut v_sec_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsec_8997_: u32 = 0;
    let mut v___x_8998_: u8 = 0;
    v_sec_8994_ = lean_ctor_get(v_x_8992_, 0);
    v_nsec_8995_ = lean_ctor_get_uint32(
        v_x_8992_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_sec_8996_ = lean_ctor_get(v_x_8993_, 0);
    v_nsec_8997_ = lean_ctor_get_uint32(
        v_x_8993_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_8998_ = lean_int_dec_lt(v_sec_8994_, v_sec_8996_);
    if v___x_8998_ == 0 {
        let mut v___x_8999_: u8 = 0;
        v___x_8999_ = lean_int_dec_eq(v_sec_8994_, v_sec_8996_);
        if v___x_8999_ == 0 {
            let mut v___x_9000_: u8 = 0;
            v___x_9000_ = 2;
            return v___x_9000_;
        } else {
            let mut v___x_9001_: u8 = 0;
            v___x_9001_ = lean_uint32_dec_lt(v_nsec_8995_, v_nsec_8997_);
            if v___x_9001_ == 0 {
                let mut v___x_9002_: u8 = 0;
                v___x_9002_ = lean_uint32_dec_eq(v_nsec_8995_, v_nsec_8997_);
                if v___x_9002_ == 0 {
                    let mut v___x_9003_: u8 = 0;
                    v___x_9003_ = 2;
                    return v___x_9003_;
                } else {
                    let mut v___x_9004_: u8 = 0;
                    v___x_9004_ = 1;
                    return v___x_9004_;
                }
            } else {
                let mut v___x_9005_: u8 = 0;
                v___x_9005_ = 0;
                return v___x_9005_;
            }
        }
    } else {
        let mut v___x_9006_: u8 = 0;
        v___x_9006_ = 0;
        return v___x_9006_;
    }
}
pub unsafe fn l_IO_FS_instOrdSystemTime_ord___boxed(
    mut v_x_9007_: *mut LeanObject,
    mut v_x_9008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9009_: u8 = 0;
    let mut v_r_9010_: *mut LeanObject = core::ptr::null_mut();
    v_res_9009_ = l_IO_FS_instOrdSystemTime_ord(v_x_9007_, v_x_9008_);
    lean_dec_ref(v_x_9008_);
    lean_dec_ref(v_x_9007_);
    v_r_9010_ = lean_box((v_res_9009_) as usize);
    return v_r_9010_;
}
pub unsafe fn _init_l_IO_FS_instInhabitedSystemTime_default___closed__0() -> u32 {
    let mut v___x_9013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9014_: u32 = 0;
    v___x_9013_ = lean_unsigned_to_nat(0);
    v___x_9014_ = lean_uint32_of_nat(v___x_9013_);
    return v___x_9014_;
}
pub unsafe fn _init_l_IO_FS_instInhabitedSystemTime_default___closed__1() -> *mut LeanObject {
    let mut v___x_9015_: u32 = 0;
    let mut v___x_9016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9017_: *mut LeanObject = core::ptr::null_mut();
    v___x_9015_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_IO_FS_instInhabitedSystemTime_default___closed__0),
        core::ptr::addr_of_mut!(l_IO_FS_instInhabitedSystemTime_default___closed__0_once),
        _init_l_IO_FS_instInhabitedSystemTime_default___closed__0,
    );
    v___x_9016_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instReprSystemTime_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once),
        _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7,
    );
    v___x_9017_ = lean_alloc_ctor(0, 1, (4) as u32);
    lean_ctor_set(v___x_9017_, 0, v___x_9016_);
    lean_ctor_set_uint32(
        v___x_9017_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9015_,
    );
    return v___x_9017_;
}
pub unsafe fn _init_l_IO_FS_instInhabitedSystemTime_default() -> *mut LeanObject {
    let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
    v___x_9018_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instInhabitedSystemTime_default___closed__1),
        core::ptr::addr_of_mut!(l_IO_FS_instInhabitedSystemTime_default___closed__1_once),
        _init_l_IO_FS_instInhabitedSystemTime_default___closed__1,
    );
    return v___x_9018_;
}
pub unsafe fn _init_l_IO_FS_instInhabitedSystemTime() -> *mut LeanObject {
    let mut v___x_9019_: *mut LeanObject = core::ptr::null_mut();
    v___x_9019_ = l_IO_FS_instInhabitedSystemTime_default;
    return v___x_9019_;
}
pub unsafe fn _init_l_IO_FS_instLTSystemTime() -> *mut LeanObject {
    let mut v___x_9020_: *mut LeanObject = core::ptr::null_mut();
    v___x_9020_ = lean_box(0);
    return v___x_9020_;
}
pub unsafe fn _init_l_IO_FS_instLESystemTime() -> *mut LeanObject {
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    v___x_9021_ = lean_box(0);
    return v___x_9021_;
}
pub unsafe fn l_IO_FS_instReprMetadata_repr___redArg(
    mut v_x_9043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_accessed_9044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modified_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_byteSize_9046_: u64 = 0;
    let mut v_type_9047_: u8 = 0;
    let mut v_numLinks_9048_: u64 = 0;
    let mut v___x_9049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9055_: u8 = 0;
    let mut v___x_9056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut LeanObject = core::ptr::null_mut();
    v_accessed_9044_ = lean_ctor_get(v_x_9043_, 0);
    v_modified_9045_ = lean_ctor_get(v_x_9043_, 1);
    v_byteSize_9046_ = lean_ctor_get_uint64(
        v_x_9043_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_type_9047_ = lean_ctor_get_uint8(
        v_x_9043_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
    );
    v_numLinks_9048_ = lean_ctor_get_uint64(
        v_x_9043_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 8) as u32,
    );
    v___x_9049_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__5;
    v___x_9050_ = l_IO_FS_instReprMetadata_repr___redArg___closed__3;
    v___x_9051_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once),
        _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14,
    );
    v___x_9052_ = lean_unsigned_to_nat(0);
    v___x_9053_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_9044_);
    v___x_9054_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9054_, 0, v___x_9051_);
    lean_ctor_set(v___x_9054_, 1, v___x_9053_);
    v___x_9055_ = 0;
    v___x_9056_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9056_, 0, v___x_9054_);
    lean_ctor_set_uint8(
        v___x_9056_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    v___x_9057_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9057_, 0, v___x_9050_);
    lean_ctor_set(v___x_9057_, 1, v___x_9056_);
    v___x_9058_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__11;
    v___x_9059_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9059_, 0, v___x_9057_);
    lean_ctor_set(v___x_9059_, 1, v___x_9058_);
    v___x_9060_ = lean_box(1);
    v___x_9061_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9061_, 0, v___x_9059_);
    lean_ctor_set(v___x_9061_, 1, v___x_9060_);
    v___x_9062_ = l_IO_FS_instReprMetadata_repr___redArg___closed__5;
    v___x_9063_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9063_, 0, v___x_9061_);
    lean_ctor_set(v___x_9063_, 1, v___x_9062_);
    v___x_9064_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9064_, 0, v___x_9063_);
    lean_ctor_set(v___x_9064_, 1, v___x_9049_);
    v___x_9065_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_9045_);
    v___x_9066_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9066_, 0, v___x_9051_);
    lean_ctor_set(v___x_9066_, 1, v___x_9065_);
    v___x_9067_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9067_, 0, v___x_9066_);
    lean_ctor_set_uint8(
        v___x_9067_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    v___x_9068_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9068_, 0, v___x_9064_);
    lean_ctor_set(v___x_9068_, 1, v___x_9067_);
    v___x_9069_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9069_, 0, v___x_9068_);
    lean_ctor_set(v___x_9069_, 1, v___x_9058_);
    v___x_9070_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9070_, 0, v___x_9069_);
    lean_ctor_set(v___x_9070_, 1, v___x_9060_);
    v___x_9071_ = l_IO_FS_instReprMetadata_repr___redArg___closed__7;
    v___x_9072_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9072_, 0, v___x_9070_);
    lean_ctor_set(v___x_9072_, 1, v___x_9071_);
    v___x_9073_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9073_, 0, v___x_9072_);
    lean_ctor_set(v___x_9073_, 1, v___x_9049_);
    v___x_9074_ = lean_uint64_to_nat(v_byteSize_9046_);
    v___x_9075_ = l_Nat_reprFast(v___x_9074_);
    v___x_9076_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_9076_, 0, v___x_9075_);
    v___x_9077_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9077_, 0, v___x_9051_);
    lean_ctor_set(v___x_9077_, 1, v___x_9076_);
    v___x_9078_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9078_, 0, v___x_9077_);
    lean_ctor_set_uint8(
        v___x_9078_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    v___x_9079_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9079_, 0, v___x_9073_);
    lean_ctor_set(v___x_9079_, 1, v___x_9078_);
    v___x_9080_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9080_, 0, v___x_9079_);
    lean_ctor_set(v___x_9080_, 1, v___x_9058_);
    v___x_9081_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9081_, 0, v___x_9080_);
    lean_ctor_set(v___x_9081_, 1, v___x_9060_);
    v___x_9082_ = l_IO_FS_instReprMetadata_repr___redArg___closed__9;
    v___x_9083_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9083_, 0, v___x_9081_);
    lean_ctor_set(v___x_9083_, 1, v___x_9082_);
    v___x_9084_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9084_, 0, v___x_9083_);
    lean_ctor_set(v___x_9084_, 1, v___x_9049_);
    v___x_9085_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once),
        _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7,
    );
    v___x_9086_ = l_IO_FS_instReprFileType_repr(v_type_9047_, v___x_9052_);
    v___x_9087_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9087_, 0, v___x_9085_);
    lean_ctor_set(v___x_9087_, 1, v___x_9086_);
    v___x_9088_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9088_, 0, v___x_9087_);
    lean_ctor_set_uint8(
        v___x_9088_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    v___x_9089_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9089_, 0, v___x_9084_);
    lean_ctor_set(v___x_9089_, 1, v___x_9088_);
    v___x_9090_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9090_, 0, v___x_9089_);
    lean_ctor_set(v___x_9090_, 1, v___x_9058_);
    v___x_9091_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9091_, 0, v___x_9090_);
    lean_ctor_set(v___x_9091_, 1, v___x_9060_);
    v___x_9092_ = l_IO_FS_instReprMetadata_repr___redArg___closed__11;
    v___x_9093_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9093_, 0, v___x_9091_);
    lean_ctor_set(v___x_9093_, 1, v___x_9092_);
    v___x_9094_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9094_, 0, v___x_9093_);
    lean_ctor_set(v___x_9094_, 1, v___x_9049_);
    v___x_9095_ = lean_uint64_to_nat(v_numLinks_9048_);
    v___x_9096_ = l_Nat_reprFast(v___x_9095_);
    v___x_9097_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_9097_, 0, v___x_9096_);
    v___x_9098_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9098_, 0, v___x_9051_);
    lean_ctor_set(v___x_9098_, 1, v___x_9097_);
    v___x_9099_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9099_, 0, v___x_9098_);
    lean_ctor_set_uint8(
        v___x_9099_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    v___x_9100_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9100_, 0, v___x_9094_);
    lean_ctor_set(v___x_9100_, 1, v___x_9099_);
    v___x_9101_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once),
        _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17,
    );
    v___x_9102_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__18;
    v___x_9103_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9103_, 0, v___x_9102_);
    lean_ctor_set(v___x_9103_, 1, v___x_9100_);
    v___x_9104_ = l_IO_FS_instReprDirEntry_repr___redArg___closed__19;
    v___x_9105_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_9105_, 0, v___x_9103_);
    lean_ctor_set(v___x_9105_, 1, v___x_9104_);
    v___x_9106_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_9106_, 0, v___x_9101_);
    lean_ctor_set(v___x_9106_, 1, v___x_9105_);
    v___x_9107_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_9107_, 0, v___x_9106_);
    lean_ctor_set_uint8(
        v___x_9107_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_9055_,
    );
    return v___x_9107_;
}
pub unsafe fn l_IO_FS_instReprMetadata_repr___redArg___boxed(
    mut v_x_9108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9109_: *mut LeanObject = core::ptr::null_mut();
    v_res_9109_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_9108_);
    lean_dec_ref(v_x_9108_);
    return v_res_9109_;
}
pub unsafe fn l_IO_FS_instReprMetadata_repr(
    mut v_x_9110_: *mut LeanObject,
    mut v_prec_9111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9112_: *mut LeanObject = core::ptr::null_mut();
    v___x_9112_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_9110_);
    return v___x_9112_;
}
pub unsafe fn l_IO_FS_instReprMetadata_repr___boxed(
    mut v_x_9113_: *mut LeanObject,
    mut v_prec_9114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9115_: *mut LeanObject = core::ptr::null_mut();
    v_res_9115_ = l_IO_FS_instReprMetadata_repr(v_x_9113_, v_prec_9114_);
    lean_dec(v_prec_9114_);
    lean_dec_ref(v_x_9113_);
    return v_res_9115_;
}
pub unsafe fn l_System_FilePath_readDir___boxed(
    mut v_a_00___x40___internal___hyg_9120_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9122_: *mut LeanObject = core::ptr::null_mut();
    v_res_9122_ = lean_io_read_dir(v_a_00___x40___internal___hyg_9120_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9120_);
    return v_res_9122_;
}
pub unsafe fn l_System_FilePath_metadata___boxed(
    mut v_a_00___x40___internal___hyg_9125_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9127_: *mut LeanObject = core::ptr::null_mut();
    v_res_9127_ = lean_io_metadata(v_a_00___x40___internal___hyg_9125_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9125_);
    return v_res_9127_;
}
pub unsafe fn l_System_FilePath_symlinkMetadata___boxed(
    mut v_a_00___x40___internal___hyg_9130_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9132_: *mut LeanObject = core::ptr::null_mut();
    v_res_9132_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_9130_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9130_);
    return v_res_9132_;
}
pub unsafe fn l_System_FilePath_isDir(mut v_p_9133_: *mut LeanObject) -> u8 {
    let mut v___x_9135_: *mut LeanObject = core::ptr::null_mut();
    v___x_9135_ = lean_io_metadata(v_p_9133_);
    if lean_obj_tag(v___x_9135_) == 0 {
        let mut v_a_9136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_9137_: u8 = 0;
        let mut v___x_9138_: u8 = 0;
        let mut v___x_9139_: u8 = 0;
        v_a_9136_ = lean_ctor_get(v___x_9135_, 0);
        lean_inc(v_a_9136_);
        lean_dec_ref_known(v___x_9135_, 1);
        v_type_9137_ = lean_ctor_get_uint8(
            v_a_9136_,
            (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
        );
        lean_dec(v_a_9136_);
        v___x_9138_ = 0;
        v___x_9139_ = l_IO_FS_instBEqFileType_beq(v_type_9137_, v___x_9138_);
        return v___x_9139_;
    } else {
        let mut v___x_9140_: u8 = 0;
        lean_dec_ref_known(v___x_9135_, 1);
        v___x_9140_ = 0;
        return v___x_9140_;
    }
}
pub unsafe fn l_System_FilePath_isDir___boxed(
    mut v_p_9141_: *mut LeanObject,
    mut v_a_9142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9143_: u8 = 0;
    let mut v_r_9144_: *mut LeanObject = core::ptr::null_mut();
    v_res_9143_ = l_System_FilePath_isDir(v_p_9141_);
    lean_dec_ref(v_p_9141_);
    v_r_9144_ = lean_box((v_res_9143_) as usize);
    return v_r_9144_;
}
pub unsafe fn l_System_FilePath_pathExists(mut v_p_9145_: *mut LeanObject) -> u8 {
    let mut v___x_9147_: *mut LeanObject = core::ptr::null_mut();
    v___x_9147_ = lean_io_metadata(v_p_9145_);
    if lean_obj_tag(v___x_9147_) == 0 {
        let mut v___x_9148_: u8 = 0;
        lean_dec_ref_known(v___x_9147_, 1);
        v___x_9148_ = 1;
        return v___x_9148_;
    } else {
        let mut v___x_9149_: u8 = 0;
        lean_dec_ref_known(v___x_9147_, 1);
        v___x_9149_ = 0;
        return v___x_9149_;
    }
}
pub unsafe fn l_System_FilePath_pathExists___boxed(
    mut v_p_9150_: *mut LeanObject,
    mut v_a_9151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9152_: u8 = 0;
    let mut v_r_9153_: *mut LeanObject = core::ptr::null_mut();
    v_res_9152_ = l_System_FilePath_pathExists(v_p_9150_);
    lean_dec_ref(v_p_9150_);
    v_r_9153_ = lean_box((v_res_9152_) as usize);
    return v_r_9153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(
    mut v_enter_9154_: *mut LeanObject,
    mut v_p_9155_: *mut LeanObject,
    mut v_as_9156_: *mut LeanObject,
    mut v_sz_9157_: usize,
    mut v_i_9158_: usize,
    mut v_b_9159_: *mut LeanObject,
    mut v___y_9160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9165_: usize = 0;
    let mut v___x_9166_: usize = 0;
    let mut v___x_9168_: u8 = 0;
    let mut v___x_9169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9177_: u8 = 0;
    let mut v___x_9178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9180_: u8 = 0;
    let mut v___x_9181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9183_: u8 = 0;
    let mut v___x_9184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9190_: u8 = 0;
    let mut v___x_9192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9194_: u8 = 0;
    let mut v_a_9195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9198_: u8 = 0;
    let mut v___x_9200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9202_: u8 = 0;
    let mut v___x_9203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9209_: u8 = 0;
    let mut v___x_9211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9168_ = lean_usize_dec_lt(v_i_9158_, v_sz_9157_);
                if v___x_9168_ == 0 {
                    lean_dec_ref(v_p_9155_);
                    lean_dec_ref(v_enter_9154_);
                    v___x_9169_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9169_, 0, v_b_9159_);
                    lean_ctor_set(v___x_9169_, 1, v___y_9160_);
                    v___x_9170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9170_, 0, v___x_9169_);
                    return v___x_9170_;
                } else {
                    v___x_9171_ = lean_box(0);
                    v_a_9172_ = lean_array_uget_borrowed(v_as_9156_, v_i_9158_);
                    lean_inc(v_a_9172_);
                    v___x_9173_ = l_IO_FS_DirEntry_path(v_a_9172_);
                    lean_inc_ref(v___x_9173_);
                    v___x_9174_ = lean_array_push(v___y_9160_, v___x_9173_);
                    v___x_9175_ = lean_io_metadata(v___x_9173_);
                    if lean_obj_tag(v___x_9175_) == 0 {
                        v_a_9176_ = lean_ctor_get(v___x_9175_, 0);
                        lean_inc(v_a_9176_);
                        lean_dec_ref_known(v___x_9175_, 1);
                        v_type_9177_ = lean_ctor_get_uint8(
                            v_a_9176_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
                        );
                        lean_dec(v_a_9176_);
                        match v_type_9177_ {
                            2 => {
                                v___x_9178_ = lean_io_realpath(v___x_9173_);
                                if lean_obj_tag(v___x_9178_) == 0 {
                                    v_a_9179_ = lean_ctor_get(v___x_9178_, 0);
                                    lean_inc(v_a_9179_);
                                    lean_dec_ref_known(v___x_9178_, 1);
                                    v___x_9180_ = l_System_FilePath_isDir(v_a_9179_);
                                    if v___x_9180_ == 0 {
                                        lean_dec(v_a_9179_);
                                        v_a_9163_ = v___x_9171_;
                                        v_snd_9164_ = v___x_9174_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc_ref(v_enter_9154_);
                                        lean_inc_ref(v_p_9155_);
                                        v___x_9181_ =
                                            lean_apply_2(v_enter_9154_, v_p_9155_, lean_box(0));
                                        if lean_obj_tag(v___x_9181_) == 0 {
                                            v_a_9182_ = lean_ctor_get(v___x_9181_, 0);
                                            lean_inc(v_a_9182_);
                                            lean_dec_ref_known(v___x_9181_, 1);
                                            v___x_9183_ = (lean_unbox(v_a_9182_) as u8);
                                            lean_dec(v_a_9182_);
                                            if v___x_9183_ == 0 {
                                                lean_dec(v_a_9179_);
                                                v_a_9163_ = v___x_9171_;
                                                v_snd_9164_ = v___x_9174_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc_ref(v_enter_9154_);
                                                v___x_9184_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_9154_, v_a_9179_, v___x_9174_);
                                                if lean_obj_tag(v___x_9184_) == 0 {
                                                    v_a_9185_ = lean_ctor_get(v___x_9184_, 0);
                                                    lean_inc(v_a_9185_);
                                                    lean_dec_ref_known(v___x_9184_, 1);
                                                    v_snd_9186_ = lean_ctor_get(v_a_9185_, 1);
                                                    lean_inc(v_snd_9186_);
                                                    lean_dec(v_a_9185_);
                                                    v_a_9163_ = v___x_9171_;
                                                    v_snd_9164_ = v_snd_9186_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v_p_9155_);
                                                    lean_dec_ref(v_enter_9154_);
                                                    return v___x_9184_;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_9179_);
                                            lean_dec_ref(v___x_9174_);
                                            lean_dec_ref(v_p_9155_);
                                            lean_dec_ref(v_enter_9154_);
                                            v_a_9187_ = lean_ctor_get(v___x_9181_, 0);
                                            v_isSharedCheck_9194_ =
                                                (!lean_is_exclusive(v___x_9181_)) as u8;
                                            if v_isSharedCheck_9194_ == 0 {
                                                v___x_9189_ = v___x_9181_;
                                                v_isShared_9190_ = v_isSharedCheck_9194_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_9187_);
                                                lean_dec(v___x_9181_);
                                                v___x_9189_ = lean_box(0);
                                                v_isShared_9190_ = v_isSharedCheck_9194_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_9174_);
                                    lean_dec_ref(v_p_9155_);
                                    lean_dec_ref(v_enter_9154_);
                                    v_a_9195_ = lean_ctor_get(v___x_9178_, 0);
                                    v_isSharedCheck_9202_ = (!lean_is_exclusive(v___x_9178_)) as u8;
                                    if v_isSharedCheck_9202_ == 0 {
                                        v___x_9197_ = v___x_9178_;
                                        v_isShared_9198_ = v_isSharedCheck_9202_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_9195_);
                                        lean_dec(v___x_9178_);
                                        v___x_9197_ = lean_box(0);
                                        v_isShared_9198_ = v_isSharedCheck_9202_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                            0 => {
                                lean_inc_ref(v_enter_9154_);
                                v___x_9203_ =
                                    l___private_Init_System_IO_0__System_FilePath_walkDir_go(
                                        v_enter_9154_,
                                        v___x_9173_,
                                        v___x_9174_,
                                    );
                                if lean_obj_tag(v___x_9203_) == 0 {
                                    v_a_9204_ = lean_ctor_get(v___x_9203_, 0);
                                    lean_inc(v_a_9204_);
                                    lean_dec_ref_known(v___x_9203_, 1);
                                    v_snd_9205_ = lean_ctor_get(v_a_9204_, 1);
                                    lean_inc(v_snd_9205_);
                                    lean_dec(v_a_9204_);
                                    v_a_9163_ = v___x_9171_;
                                    v_snd_9164_ = v_snd_9205_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_p_9155_);
                                    lean_dec_ref(v_enter_9154_);
                                    return v___x_9203_;
                                }
                            }
                            _ => {
                                lean_dec_ref(v___x_9173_);
                                v_a_9163_ = v___x_9171_;
                                v_snd_9164_ = v___x_9174_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_9173_);
                        v_a_9206_ = lean_ctor_get(v___x_9175_, 0);
                        v_isSharedCheck_9213_ = (!lean_is_exclusive(v___x_9175_)) as u8;
                        if v_isSharedCheck_9213_ == 0 {
                            v___x_9208_ = v___x_9175_;
                            v_isShared_9209_ = v_isSharedCheck_9213_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9206_);
                            lean_dec(v___x_9175_);
                            v___x_9208_ = lean_box(0);
                            v_isShared_9209_ = v_isSharedCheck_9213_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_9165_ = 1usize;
                v___x_9166_ = lean_usize_add(v_i_9158_, v___x_9165_);
                v_i_9158_ = v___x_9166_;
                v_b_9159_ = v_a_9163_;
                v___y_9160_ = v_snd_9164_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_9190_ == 0 {
                    v___x_9192_ = v___x_9189_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9193_, 0, v_a_9187_);
                    v___x_9192_ = v_reuseFailAlloc_9193_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9192_;
            }
            4 => {
                if v_isShared_9198_ == 0 {
                    v___x_9200_ = v___x_9197_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9201_, 0, v_a_9195_);
                    v___x_9200_ = v_reuseFailAlloc_9201_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9200_;
            }
            6 => {
                if lean_obj_tag(v_a_9206_) == 11 {
                    lean_dec_ref_known(v_a_9206_, 2);
                    lean_del_object(v___x_9208_);
                    v_a_9163_ = v___x_9171_;
                    v_snd_9164_ = v___x_9174_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_9174_);
                    lean_dec_ref(v_p_9155_);
                    lean_dec_ref(v_enter_9154_);
                    if v_isShared_9209_ == 0 {
                        v___x_9211_ = v___x_9208_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_9212_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9212_, 0, v_a_9206_);
                        v___x_9211_ = v_reuseFailAlloc_9212_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_9211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__System_FilePath_walkDir_go(
    mut v_enter_9214_: *mut LeanObject,
    mut v_p_9215_: *mut LeanObject,
    mut v_a_9216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9222_: u8 = 0;
    let mut v___x_9223_: u8 = 0;
    let mut v___x_9224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9232_: usize = 0;
    let mut v___x_9233_: usize = 0;
    let mut v___x_9234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9238_: u8 = 0;
    let mut v_snd_9239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9242_: u8 = 0;
    let mut v___x_9244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9249_: u8 = 0;
    let mut v_unused_9250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9251_: u8 = 0;
    let mut v_a_9252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9255_: u8 = 0;
    let mut v___x_9257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9259_: u8 = 0;
    let mut v_isSharedCheck_9260_: u8 = 0;
    let mut v_a_9261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9264_: u8 = 0;
    let mut v___x_9266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_enter_9214_);
                lean_inc_ref(v_p_9215_);
                v___x_9218_ = lean_apply_2(v_enter_9214_, v_p_9215_, lean_box(0));
                if lean_obj_tag(v___x_9218_) == 0 {
                    v_a_9219_ = lean_ctor_get(v___x_9218_, 0);
                    v_isSharedCheck_9260_ = (!lean_is_exclusive(v___x_9218_)) as u8;
                    if v_isSharedCheck_9260_ == 0 {
                        v___x_9221_ = v___x_9218_;
                        v_isShared_9222_ = v_isSharedCheck_9260_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9219_);
                        lean_dec(v___x_9218_);
                        v___x_9221_ = lean_box(0);
                        v_isShared_9222_ = v_isSharedCheck_9260_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_9216_);
                    lean_dec_ref(v_p_9215_);
                    lean_dec_ref(v_enter_9214_);
                    v_a_9261_ = lean_ctor_get(v___x_9218_, 0);
                    v_isSharedCheck_9268_ = (!lean_is_exclusive(v___x_9218_)) as u8;
                    if v_isSharedCheck_9268_ == 0 {
                        v___x_9263_ = v___x_9218_;
                        v_isShared_9264_ = v_isSharedCheck_9268_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_9261_);
                        lean_dec(v___x_9218_);
                        v___x_9263_ = lean_box(0);
                        v_isShared_9264_ = v_isSharedCheck_9268_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9223_ = (lean_unbox(v_a_9219_) as u8);
                lean_dec(v_a_9219_);
                if v___x_9223_ == 0 {
                    lean_dec_ref(v_p_9215_);
                    lean_dec_ref(v_enter_9214_);
                    v___x_9224_ = lean_box(0);
                    v___x_9225_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9225_, 0, v___x_9224_);
                    lean_ctor_set(v___x_9225_, 1, v_a_9216_);
                    if v_isShared_9222_ == 0 {
                        lean_ctor_set(v___x_9221_, 0, v___x_9225_);
                        v___x_9227_ = v___x_9221_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9228_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9228_, 0, v___x_9225_);
                        v___x_9227_ = v_reuseFailAlloc_9228_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9221_);
                    v___x_9229_ = lean_io_read_dir(v_p_9215_);
                    if lean_obj_tag(v___x_9229_) == 0 {
                        v_a_9230_ = lean_ctor_get(v___x_9229_, 0);
                        lean_inc(v_a_9230_);
                        lean_dec_ref_known(v___x_9229_, 1);
                        v___x_9231_ = lean_box(0);
                        v_sz_9232_ = lean_array_size(v_a_9230_);
                        v___x_9233_ = 0usize;
                        v___x_9234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_9214_, v_p_9215_, v_a_9230_, v_sz_9232_, v___x_9233_, v___x_9231_, v_a_9216_);
                        lean_dec(v_a_9230_);
                        if lean_obj_tag(v___x_9234_) == 0 {
                            v_a_9235_ = lean_ctor_get(v___x_9234_, 0);
                            v_isSharedCheck_9251_ = (!lean_is_exclusive(v___x_9234_)) as u8;
                            if v_isSharedCheck_9251_ == 0 {
                                v___x_9237_ = v___x_9234_;
                                v_isShared_9238_ = v_isSharedCheck_9251_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_9235_);
                                lean_dec(v___x_9234_);
                                v___x_9237_ = lean_box(0);
                                v_isShared_9238_ = v_isSharedCheck_9251_;
                                state = 3;
                                continue;
                            }
                        } else {
                            return v___x_9234_;
                        }
                    } else {
                        lean_dec_ref(v_a_9216_);
                        lean_dec_ref(v_p_9215_);
                        lean_dec_ref(v_enter_9214_);
                        v_a_9252_ = lean_ctor_get(v___x_9229_, 0);
                        v_isSharedCheck_9259_ = (!lean_is_exclusive(v___x_9229_)) as u8;
                        if v_isSharedCheck_9259_ == 0 {
                            v___x_9254_ = v___x_9229_;
                            v_isShared_9255_ = v_isSharedCheck_9259_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_9252_);
                            lean_dec(v___x_9229_);
                            v___x_9254_ = lean_box(0);
                            v_isShared_9255_ = v_isSharedCheck_9259_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_9227_;
            }
            3 => {
                v_snd_9239_ = lean_ctor_get(v_a_9235_, 1);
                v_isSharedCheck_9249_ = (!lean_is_exclusive(v_a_9235_)) as u8;
                if v_isSharedCheck_9249_ == 0 {
                    v_unused_9250_ = lean_ctor_get(v_a_9235_, 0);
                    lean_dec(v_unused_9250_);
                    v___x_9241_ = v_a_9235_;
                    v_isShared_9242_ = v_isSharedCheck_9249_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_9239_);
                    lean_dec(v_a_9235_);
                    v___x_9241_ = lean_box(0);
                    v_isShared_9242_ = v_isSharedCheck_9249_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_9242_ == 0 {
                    lean_ctor_set(v___x_9241_, 0, v___x_9231_);
                    v___x_9244_ = v___x_9241_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9248_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9248_, 0, v___x_9231_);
                    lean_ctor_set(v_reuseFailAlloc_9248_, 1, v_snd_9239_);
                    v___x_9244_ = v_reuseFailAlloc_9248_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_9238_ == 0 {
                    lean_ctor_set(v___x_9237_, 0, v___x_9244_);
                    v___x_9246_ = v___x_9237_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9247_, 0, v___x_9244_);
                    v___x_9246_ = v_reuseFailAlloc_9247_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9246_;
            }
            7 => {
                if v_isShared_9255_ == 0 {
                    v___x_9257_ = v___x_9254_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9258_, 0, v_a_9252_);
                    v___x_9257_ = v_reuseFailAlloc_9258_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9257_;
            }
            9 => {
                if v_isShared_9264_ == 0 {
                    v___x_9266_ = v___x_9263_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9267_, 0, v_a_9261_);
                    v___x_9266_ = v_reuseFailAlloc_9267_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(
    mut v_enter_9269_: *mut LeanObject,
    mut v_p_9270_: *mut LeanObject,
    mut v_a_9271_: *mut LeanObject,
    mut v_a_9272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9273_: *mut LeanObject = core::ptr::null_mut();
    v_res_9273_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(
        v_enter_9269_,
        v_p_9270_,
        v_a_9271_,
    );
    return v_res_9273_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(
    mut v_enter_9274_: *mut LeanObject,
    mut v_p_9275_: *mut LeanObject,
    mut v_as_9276_: *mut LeanObject,
    mut v_sz_9277_: *mut LeanObject,
    mut v_i_9278_: *mut LeanObject,
    mut v_b_9279_: *mut LeanObject,
    mut v___y_9280_: *mut LeanObject,
    mut v___y_9281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9282_: usize = 0;
    let mut v_i_boxed_9283_: usize = 0;
    let mut v_res_9284_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9282_ = lean_unbox_usize(v_sz_9277_);
    lean_dec(v_sz_9277_);
    v_i_boxed_9283_ = lean_unbox_usize(v_i_9278_);
    lean_dec(v_i_9278_);
    v_res_9284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_9274_, v_p_9275_, v_as_9276_, v_sz_boxed_9282_, v_i_boxed_9283_, v_b_9279_, v___y_9280_);
    lean_dec_ref(v_as_9276_);
    return v_res_9284_;
}
pub unsafe fn l_System_FilePath_walkDir(
    mut v_p_9285_: *mut LeanObject,
    mut v_enter_9286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9293_: u8 = 0;
    let mut v_snd_9294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9298_: u8 = 0;
    let mut v_a_9299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9302_: u8 = 0;
    let mut v___x_9304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9288_ = l_IO_FS_Handle_lines___closed__0;
                v___x_9289_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(
                    v_enter_9286_,
                    v_p_9285_,
                    v___x_9288_,
                );
                if lean_obj_tag(v___x_9289_) == 0 {
                    v_a_9290_ = lean_ctor_get(v___x_9289_, 0);
                    v_isSharedCheck_9298_ = (!lean_is_exclusive(v___x_9289_)) as u8;
                    if v_isSharedCheck_9298_ == 0 {
                        v___x_9292_ = v___x_9289_;
                        v_isShared_9293_ = v_isSharedCheck_9298_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9290_);
                        lean_dec(v___x_9289_);
                        v___x_9292_ = lean_box(0);
                        v_isShared_9293_ = v_isSharedCheck_9298_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9299_ = lean_ctor_get(v___x_9289_, 0);
                    v_isSharedCheck_9306_ = (!lean_is_exclusive(v___x_9289_)) as u8;
                    if v_isSharedCheck_9306_ == 0 {
                        v___x_9301_ = v___x_9289_;
                        v_isShared_9302_ = v_isSharedCheck_9306_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9299_);
                        lean_dec(v___x_9289_);
                        v___x_9301_ = lean_box(0);
                        v_isShared_9302_ = v_isSharedCheck_9306_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_9294_ = lean_ctor_get(v_a_9290_, 1);
                lean_inc(v_snd_9294_);
                lean_dec(v_a_9290_);
                if v_isShared_9293_ == 0 {
                    lean_ctor_set(v___x_9292_, 0, v_snd_9294_);
                    v___x_9296_ = v___x_9292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9297_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9297_, 0, v_snd_9294_);
                    v___x_9296_ = v_reuseFailAlloc_9297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9296_;
            }
            3 => {
                if v_isShared_9302_ == 0 {
                    v___x_9304_ = v___x_9301_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9305_, 0, v_a_9299_);
                    v___x_9304_ = v_reuseFailAlloc_9305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_walkDir___boxed(
    mut v_p_9307_: *mut LeanObject,
    mut v_enter_9308_: *mut LeanObject,
    mut v_a_9309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9310_: *mut LeanObject = core::ptr::null_mut();
    v_res_9310_ = l_System_FilePath_walkDir(v_p_9307_, v_enter_9308_);
    return v_res_9310_;
}
pub unsafe fn _init_l_IO_FS_readBinFile___closed__0() -> *mut LeanObject {
    let mut v___x_9311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9312_: *mut LeanObject = core::ptr::null_mut();
    v___x_9311_ = lean_unsigned_to_nat(0);
    v___x_9312_ = lean_mk_empty_byte_array(v___x_9311_);
    return v___x_9312_;
}
pub unsafe fn l_IO_FS_readBinFile(mut v_fname_9313_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: u8 = 0;
    let mut v___x_9318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_byteSize_9320_: u64 = 0;
    let mut v___x_9321_: usize = 0;
    let mut v___x_9322_: usize = 0;
    let mut v___x_9323_: u8 = 0;
    let mut v___x_9324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9332_: u8 = 0;
    let mut v___x_9334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9336_: u8 = 0;
    let mut v_a_9337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9340_: u8 = 0;
    let mut v___x_9342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9315_ = lean_io_metadata(v_fname_9313_);
                if lean_obj_tag(v___x_9315_) == 0 {
                    v_a_9316_ = lean_ctor_get(v___x_9315_, 0);
                    lean_inc(v_a_9316_);
                    lean_dec_ref_known(v___x_9315_, 1);
                    v___x_9317_ = 0;
                    v___x_9318_ = lean_io_prim_handle_mk(v_fname_9313_, v___x_9317_);
                    if lean_obj_tag(v___x_9318_) == 0 {
                        v_a_9319_ = lean_ctor_get(v___x_9318_, 0);
                        lean_inc(v_a_9319_);
                        lean_dec_ref_known(v___x_9318_, 1);
                        v_byteSize_9320_ = lean_ctor_get_uint64(
                            v_a_9316_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v_a_9316_);
                        v___x_9321_ = lean_uint64_to_usize(v_byteSize_9320_);
                        v___x_9322_ = 0usize;
                        v___x_9323_ = lean_usize_dec_lt(v___x_9322_, v___x_9321_);
                        if v___x_9323_ == 0 {
                            v___x_9324_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_IO_FS_readBinFile___closed__0),
                                core::ptr::addr_of_mut!(l_IO_FS_readBinFile___closed__0_once),
                                _init_l_IO_FS_readBinFile___closed__0,
                            );
                            v___x_9325_ =
                                l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(
                                    v_a_9319_,
                                    v___x_9324_,
                                );
                            lean_dec(v_a_9319_);
                            return v___x_9325_;
                        } else {
                            v___x_9326_ = lean_io_prim_handle_read(v_a_9319_, v___x_9321_);
                            if lean_obj_tag(v___x_9326_) == 0 {
                                v_a_9327_ = lean_ctor_get(v___x_9326_, 0);
                                lean_inc(v_a_9327_);
                                lean_dec_ref_known(v___x_9326_, 1);
                                v___x_9328_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_9319_, v_a_9327_);
                                lean_dec(v_a_9319_);
                                return v___x_9328_;
                            } else {
                                lean_dec(v_a_9319_);
                                return v___x_9326_;
                            }
                        }
                    } else {
                        lean_dec(v_a_9316_);
                        v_a_9329_ = lean_ctor_get(v___x_9318_, 0);
                        v_isSharedCheck_9336_ = (!lean_is_exclusive(v___x_9318_)) as u8;
                        if v_isSharedCheck_9336_ == 0 {
                            v___x_9331_ = v___x_9318_;
                            v_isShared_9332_ = v_isSharedCheck_9336_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9329_);
                            lean_dec(v___x_9318_);
                            v___x_9331_ = lean_box(0);
                            v_isShared_9332_ = v_isSharedCheck_9336_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_9337_ = lean_ctor_get(v___x_9315_, 0);
                    v_isSharedCheck_9344_ = (!lean_is_exclusive(v___x_9315_)) as u8;
                    if v_isSharedCheck_9344_ == 0 {
                        v___x_9339_ = v___x_9315_;
                        v_isShared_9340_ = v_isSharedCheck_9344_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9337_);
                        lean_dec(v___x_9315_);
                        v___x_9339_ = lean_box(0);
                        v_isShared_9340_ = v_isSharedCheck_9344_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9332_ == 0 {
                    v___x_9334_ = v___x_9331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9335_, 0, v_a_9329_);
                    v___x_9334_ = v_reuseFailAlloc_9335_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9334_;
            }
            3 => {
                if v_isShared_9340_ == 0 {
                    v___x_9342_ = v___x_9339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9343_, 0, v_a_9337_);
                    v___x_9342_ = v_reuseFailAlloc_9343_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_readBinFile___boxed(
    mut v_fname_9345_: *mut LeanObject,
    mut v_a_9346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9347_: *mut LeanObject = core::ptr::null_mut();
    v_res_9347_ = l_IO_FS_readBinFile(v_fname_9345_);
    lean_dec_ref(v_fname_9345_);
    return v_res_9347_;
}
pub unsafe fn l_IO_FS_readFile(mut v_fname_9350_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9356_: u8 = 0;
    let mut v___x_9357_: u8 = 0;
    let mut v___x_9358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9370_: u8 = 0;
    let mut v_a_9371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9374_: u8 = 0;
    let mut v___x_9376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9352_ = l_IO_FS_readBinFile(v_fname_9350_);
                if lean_obj_tag(v___x_9352_) == 0 {
                    v_a_9353_ = lean_ctor_get(v___x_9352_, 0);
                    v_isSharedCheck_9370_ = (!lean_is_exclusive(v___x_9352_)) as u8;
                    if v_isSharedCheck_9370_ == 0 {
                        v___x_9355_ = v___x_9352_;
                        v_isShared_9356_ = v_isSharedCheck_9370_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9353_);
                        lean_dec(v___x_9352_);
                        v___x_9355_ = lean_box(0);
                        v_isShared_9356_ = v_isSharedCheck_9370_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9371_ = lean_ctor_get(v___x_9352_, 0);
                    v_isSharedCheck_9378_ = (!lean_is_exclusive(v___x_9352_)) as u8;
                    if v_isSharedCheck_9378_ == 0 {
                        v___x_9373_ = v___x_9352_;
                        v_isShared_9374_ = v_isSharedCheck_9378_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_9371_);
                        lean_dec(v___x_9352_);
                        v___x_9373_ = lean_box(0);
                        v_isShared_9374_ = v_isSharedCheck_9378_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9357_ = lean_string_validate_utf8(v_a_9353_);
                if v___x_9357_ == 0 {
                    lean_dec(v_a_9353_);
                    v___x_9358_ = l_IO_FS_readFile___closed__0;
                    v___x_9359_ = lean_string_append(v___x_9358_, v_fname_9350_);
                    v___x_9360_ = l_IO_FS_readFile___closed__1;
                    v___x_9361_ = lean_string_append(v___x_9359_, v___x_9360_);
                    v___x_9362_ = lean_alloc_ctor(18, 1, (0) as u32);
                    lean_ctor_set(v___x_9362_, 0, v___x_9361_);
                    if v_isShared_9356_ == 0 {
                        lean_ctor_set_tag(v___x_9355_, 1);
                        lean_ctor_set(v___x_9355_, 0, v___x_9362_);
                        v___x_9364_ = v___x_9355_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9365_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9365_, 0, v___x_9362_);
                        v___x_9364_ = v_reuseFailAlloc_9365_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_9366_ = lean_string_from_utf8_unchecked(v_a_9353_);
                    if v_isShared_9356_ == 0 {
                        lean_ctor_set(v___x_9355_, 0, v___x_9366_);
                        v___x_9368_ = v___x_9355_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9369_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9369_, 0, v___x_9366_);
                        v___x_9368_ = v_reuseFailAlloc_9369_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9364_;
            }
            3 => {
                return v___x_9368_;
            }
            4 => {
                if v_isShared_9374_ == 0 {
                    v___x_9376_ = v___x_9373_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9377_, 0, v_a_9371_);
                    v___x_9376_ = v_reuseFailAlloc_9377_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_readFile___boxed(
    mut v_fname_9379_: *mut LeanObject,
    mut v_a_9380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9381_: *mut LeanObject = core::ptr::null_mut();
    v_res_9381_ = l_IO_FS_readFile(v_fname_9379_);
    lean_dec_ref(v_fname_9379_);
    return v_res_9381_;
}
pub unsafe fn l_IO_withStdin___redArg___lam__0(mut v_x_9382_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_9383_: *mut LeanObject = core::ptr::null_mut();
    v_fst_9383_ = lean_ctor_get(v_x_9382_, 0);
    lean_inc(v_fst_9383_);
    return v_fst_9383_;
}
pub unsafe fn l_IO_withStdin___redArg___lam__0___boxed(
    mut v_x_9384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9385_: *mut LeanObject = core::ptr::null_mut();
    v_res_9385_ = l_IO_withStdin___redArg___lam__0(v_x_9384_);
    lean_dec_ref(v_x_9384_);
    return v_res_9385_;
}
pub unsafe fn l_IO_withStdin___redArg___lam__1(
    mut v___x_9386_: *mut LeanObject,
    mut v_x_9387_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_9386_);
    return v___x_9386_;
}
pub unsafe fn l_IO_withStdin___redArg___lam__1___boxed(
    mut v___x_9388_: *mut LeanObject,
    mut v_x_9389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9390_: *mut LeanObject = core::ptr::null_mut();
    v_res_9390_ = l_IO_withStdin___redArg___lam__1(v___x_9388_, v_x_9389_);
    lean_dec(v_x_9389_);
    lean_dec(v___x_9388_);
    return v_res_9390_;
}
pub unsafe fn l_IO_withStdin___redArg___lam__2(
    mut v_toFunctor_9391_: *mut LeanObject,
    mut v_inst_9392_: *mut LeanObject,
    mut v_inst_9393_: *mut LeanObject,
    mut v_x_9394_: *mut LeanObject,
    mut v___f_9395_: *mut LeanObject,
    mut v_prev_9396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_9397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_9398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9405_: *mut LeanObject = core::ptr::null_mut();
    v_map_9397_ = lean_ctor_get(v_toFunctor_9391_, 0);
    lean_inc(v_map_9397_);
    v_mapConst_9398_ = lean_ctor_get(v_toFunctor_9391_, 1);
    lean_inc(v_mapConst_9398_);
    lean_dec_ref(v_toFunctor_9391_);
    v___x_9399_ = lean_alloc_closure(l_IO_setStdin___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9399_, 0, v_prev_9396_);
    v___x_9400_ = lean_apply_2(v_inst_9392_, lean_box(0), v___x_9399_);
    v___x_9401_ = lean_box(0);
    v___x_9402_ = lean_apply_4(
        v_mapConst_9398_,
        lean_box(0),
        lean_box(0),
        v___x_9401_,
        v___x_9400_,
    );
    v___f_9403_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9403_, 0, v___x_9402_);
    v_y_9404_ = lean_apply_4(
        v_inst_9393_,
        lean_box(0),
        lean_box(0),
        v_x_9394_,
        v___f_9403_,
    );
    v___x_9405_ = lean_apply_4(
        v_map_9397_,
        lean_box(0),
        lean_box(0),
        v___f_9395_,
        v_y_9404_,
    );
    return v___x_9405_;
}
pub unsafe fn l_IO_withStdin___redArg(
    mut v_inst_9407_: *mut LeanObject,
    mut v_inst_9408_: *mut LeanObject,
    mut v_inst_9409_: *mut LeanObject,
    mut v_h_9410_: *mut LeanObject,
    mut v_x_9411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9419_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9412_ = lean_ctor_get(v_inst_9407_, 0);
    lean_inc_ref(v_toApplicative_9412_);
    v_toBind_9413_ = lean_ctor_get(v_inst_9407_, 1);
    lean_inc(v_toBind_9413_);
    lean_dec_ref(v_inst_9407_);
    v_toFunctor_9414_ = lean_ctor_get(v_toApplicative_9412_, 0);
    lean_inc_ref(v_toFunctor_9414_);
    lean_dec_ref(v_toApplicative_9412_);
    v___f_9415_ = l_IO_withStdin___redArg___closed__0;
    v___x_9416_ = lean_alloc_closure(l_IO_setStdin___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9416_, 0, v_h_9410_);
    lean_inc(v_inst_9409_);
    v___x_9417_ = lean_apply_2(v_inst_9409_, lean_box(0), v___x_9416_);
    v___f_9418_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_9418_, 0, v_toFunctor_9414_);
    lean_closure_set(v___f_9418_, 1, v_inst_9409_);
    lean_closure_set(v___f_9418_, 2, v_inst_9408_);
    lean_closure_set(v___f_9418_, 3, v_x_9411_);
    lean_closure_set(v___f_9418_, 4, v___f_9415_);
    v___x_9419_ = lean_apply_4(
        v_toBind_9413_,
        lean_box(0),
        lean_box(0),
        v___x_9417_,
        v___f_9418_,
    );
    return v___x_9419_;
}
pub unsafe fn l_IO_withStdin(
    mut v_m_9420_: *mut LeanObject,
    mut v_00_u03b1_9421_: *mut LeanObject,
    mut v_inst_9422_: *mut LeanObject,
    mut v_inst_9423_: *mut LeanObject,
    mut v_inst_9424_: *mut LeanObject,
    mut v_h_9425_: *mut LeanObject,
    mut v_x_9426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9427_: *mut LeanObject = core::ptr::null_mut();
    v___x_9427_ = l_IO_withStdin___redArg(
        v_inst_9422_,
        v_inst_9423_,
        v_inst_9424_,
        v_h_9425_,
        v_x_9426_,
    );
    return v___x_9427_;
}
pub unsafe fn l_IO_withStdout___redArg___lam__2(
    mut v_toFunctor_9428_: *mut LeanObject,
    mut v_inst_9429_: *mut LeanObject,
    mut v_inst_9430_: *mut LeanObject,
    mut v_x_9431_: *mut LeanObject,
    mut v___f_9432_: *mut LeanObject,
    mut v_prev_9433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_9434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_9435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9442_: *mut LeanObject = core::ptr::null_mut();
    v_map_9434_ = lean_ctor_get(v_toFunctor_9428_, 0);
    lean_inc(v_map_9434_);
    v_mapConst_9435_ = lean_ctor_get(v_toFunctor_9428_, 1);
    lean_inc(v_mapConst_9435_);
    lean_dec_ref(v_toFunctor_9428_);
    v___x_9436_ = lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9436_, 0, v_prev_9433_);
    v___x_9437_ = lean_apply_2(v_inst_9429_, lean_box(0), v___x_9436_);
    v___x_9438_ = lean_box(0);
    v___x_9439_ = lean_apply_4(
        v_mapConst_9435_,
        lean_box(0),
        lean_box(0),
        v___x_9438_,
        v___x_9437_,
    );
    v___f_9440_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9440_, 0, v___x_9439_);
    v_y_9441_ = lean_apply_4(
        v_inst_9430_,
        lean_box(0),
        lean_box(0),
        v_x_9431_,
        v___f_9440_,
    );
    v___x_9442_ = lean_apply_4(
        v_map_9434_,
        lean_box(0),
        lean_box(0),
        v___f_9432_,
        v_y_9441_,
    );
    return v___x_9442_;
}
pub unsafe fn l_IO_withStdout___redArg(
    mut v_inst_9443_: *mut LeanObject,
    mut v_inst_9444_: *mut LeanObject,
    mut v_inst_9445_: *mut LeanObject,
    mut v_h_9446_: *mut LeanObject,
    mut v_x_9447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9455_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9448_ = lean_ctor_get(v_inst_9443_, 0);
    lean_inc_ref(v_toApplicative_9448_);
    v_toBind_9449_ = lean_ctor_get(v_inst_9443_, 1);
    lean_inc(v_toBind_9449_);
    lean_dec_ref(v_inst_9443_);
    v_toFunctor_9450_ = lean_ctor_get(v_toApplicative_9448_, 0);
    lean_inc_ref(v_toFunctor_9450_);
    lean_dec_ref(v_toApplicative_9448_);
    v___f_9451_ = l_IO_withStdin___redArg___closed__0;
    v___x_9452_ = lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9452_, 0, v_h_9446_);
    lean_inc(v_inst_9445_);
    v___x_9453_ = lean_apply_2(v_inst_9445_, lean_box(0), v___x_9452_);
    v___f_9454_ = lean_alloc_closure(
        l_IO_withStdout___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_9454_, 0, v_toFunctor_9450_);
    lean_closure_set(v___f_9454_, 1, v_inst_9445_);
    lean_closure_set(v___f_9454_, 2, v_inst_9444_);
    lean_closure_set(v___f_9454_, 3, v_x_9447_);
    lean_closure_set(v___f_9454_, 4, v___f_9451_);
    v___x_9455_ = lean_apply_4(
        v_toBind_9449_,
        lean_box(0),
        lean_box(0),
        v___x_9453_,
        v___f_9454_,
    );
    return v___x_9455_;
}
pub unsafe fn l_IO_withStdout(
    mut v_m_9456_: *mut LeanObject,
    mut v_00_u03b1_9457_: *mut LeanObject,
    mut v_inst_9458_: *mut LeanObject,
    mut v_inst_9459_: *mut LeanObject,
    mut v_inst_9460_: *mut LeanObject,
    mut v_h_9461_: *mut LeanObject,
    mut v_x_9462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9463_: *mut LeanObject = core::ptr::null_mut();
    v___x_9463_ = l_IO_withStdout___redArg(
        v_inst_9458_,
        v_inst_9459_,
        v_inst_9460_,
        v_h_9461_,
        v_x_9462_,
    );
    return v___x_9463_;
}
pub unsafe fn l_IO_withStderr___redArg___lam__2(
    mut v_toFunctor_9464_: *mut LeanObject,
    mut v_inst_9465_: *mut LeanObject,
    mut v_inst_9466_: *mut LeanObject,
    mut v_x_9467_: *mut LeanObject,
    mut v___f_9468_: *mut LeanObject,
    mut v_prev_9469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_9470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_9471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9478_: *mut LeanObject = core::ptr::null_mut();
    v_map_9470_ = lean_ctor_get(v_toFunctor_9464_, 0);
    lean_inc(v_map_9470_);
    v_mapConst_9471_ = lean_ctor_get(v_toFunctor_9464_, 1);
    lean_inc(v_mapConst_9471_);
    lean_dec_ref(v_toFunctor_9464_);
    v___x_9472_ = lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9472_, 0, v_prev_9469_);
    v___x_9473_ = lean_apply_2(v_inst_9465_, lean_box(0), v___x_9472_);
    v___x_9474_ = lean_box(0);
    v___x_9475_ = lean_apply_4(
        v_mapConst_9471_,
        lean_box(0),
        lean_box(0),
        v___x_9474_,
        v___x_9473_,
    );
    v___f_9476_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9476_, 0, v___x_9475_);
    v_y_9477_ = lean_apply_4(
        v_inst_9466_,
        lean_box(0),
        lean_box(0),
        v_x_9467_,
        v___f_9476_,
    );
    v___x_9478_ = lean_apply_4(
        v_map_9470_,
        lean_box(0),
        lean_box(0),
        v___f_9468_,
        v_y_9477_,
    );
    return v___x_9478_;
}
pub unsafe fn l_IO_withStderr___redArg(
    mut v_inst_9479_: *mut LeanObject,
    mut v_inst_9480_: *mut LeanObject,
    mut v_inst_9481_: *mut LeanObject,
    mut v_h_9482_: *mut LeanObject,
    mut v_x_9483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9491_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9484_ = lean_ctor_get(v_inst_9479_, 0);
    lean_inc_ref(v_toApplicative_9484_);
    v_toBind_9485_ = lean_ctor_get(v_inst_9479_, 1);
    lean_inc(v_toBind_9485_);
    lean_dec_ref(v_inst_9479_);
    v_toFunctor_9486_ = lean_ctor_get(v_toApplicative_9484_, 0);
    lean_inc_ref(v_toFunctor_9486_);
    lean_dec_ref(v_toApplicative_9484_);
    v___f_9487_ = l_IO_withStdin___redArg___closed__0;
    v___x_9488_ = lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9488_, 0, v_h_9482_);
    lean_inc(v_inst_9481_);
    v___x_9489_ = lean_apply_2(v_inst_9481_, lean_box(0), v___x_9488_);
    v___f_9490_ = lean_alloc_closure(
        l_IO_withStderr___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_9490_, 0, v_toFunctor_9486_);
    lean_closure_set(v___f_9490_, 1, v_inst_9481_);
    lean_closure_set(v___f_9490_, 2, v_inst_9480_);
    lean_closure_set(v___f_9490_, 3, v_x_9483_);
    lean_closure_set(v___f_9490_, 4, v___f_9487_);
    v___x_9491_ = lean_apply_4(
        v_toBind_9485_,
        lean_box(0),
        lean_box(0),
        v___x_9489_,
        v___f_9490_,
    );
    return v___x_9491_;
}
pub unsafe fn l_IO_withStderr(
    mut v_m_9492_: *mut LeanObject,
    mut v_00_u03b1_9493_: *mut LeanObject,
    mut v_inst_9494_: *mut LeanObject,
    mut v_inst_9495_: *mut LeanObject,
    mut v_inst_9496_: *mut LeanObject,
    mut v_h_9497_: *mut LeanObject,
    mut v_x_9498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9499_: *mut LeanObject = core::ptr::null_mut();
    v___x_9499_ = l_IO_withStderr___redArg(
        v_inst_9494_,
        v_inst_9495_,
        v_inst_9496_,
        v_h_9497_,
        v_x_9498_,
    );
    return v___x_9499_;
}
pub unsafe fn l_IO_print___redArg(
    mut v_inst_9500_: *mut LeanObject,
    mut v_s_9501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_9504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9506_: *mut LeanObject = core::ptr::null_mut();
    v___x_9503_ = lean_get_stdout();
    v_putStr_9504_ = lean_ctor_get(v___x_9503_, 4);
    lean_inc_ref(v_putStr_9504_);
    lean_dec_ref(v___x_9503_);
    v___x_9505_ = lean_apply_1(v_inst_9500_, v_s_9501_);
    v___x_9506_ = lean_apply_2(v_putStr_9504_, v___x_9505_, lean_box(0));
    return v___x_9506_;
}
pub unsafe fn l_IO_print___redArg___boxed(
    mut v_inst_9507_: *mut LeanObject,
    mut v_s_9508_: *mut LeanObject,
    mut v_a_9509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9510_: *mut LeanObject = core::ptr::null_mut();
    v_res_9510_ = l_IO_print___redArg(v_inst_9507_, v_s_9508_);
    return v_res_9510_;
}
pub unsafe fn l_IO_print(
    mut v_00_u03b1_9511_: *mut LeanObject,
    mut v_inst_9512_: *mut LeanObject,
    mut v_s_9513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9515_: *mut LeanObject = core::ptr::null_mut();
    v___x_9515_ = l_IO_print___redArg(v_inst_9512_, v_s_9513_);
    return v___x_9515_;
}
pub unsafe fn l_IO_print___boxed(
    mut v_00_u03b1_9516_: *mut LeanObject,
    mut v_inst_9517_: *mut LeanObject,
    mut v_s_9518_: *mut LeanObject,
    mut v_a_9519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9520_: *mut LeanObject = core::ptr::null_mut();
    v_res_9520_ = l_IO_print(v_00_u03b1_9516_, v_inst_9517_, v_s_9518_);
    return v_res_9520_;
}
pub unsafe fn l_IO_println___redArg(
    mut v_inst_9522_: *mut LeanObject,
    mut v_s_9523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9527_: u32 = 0;
    let mut v___x_9528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    v___f_9525_ = l_IO_println___redArg___closed__0;
    v___x_9526_ = lean_apply_1(v_inst_9522_, v_s_9523_);
    v___x_9527_ = 10;
    v___x_9528_ = lean_string_push(v___x_9526_, v___x_9527_);
    v___x_9529_ = l_IO_print___redArg(v___f_9525_, v___x_9528_);
    return v___x_9529_;
}
pub unsafe fn l_IO_println___redArg___boxed(
    mut v_inst_9530_: *mut LeanObject,
    mut v_s_9531_: *mut LeanObject,
    mut v_a_9532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9533_: *mut LeanObject = core::ptr::null_mut();
    v_res_9533_ = l_IO_println___redArg(v_inst_9530_, v_s_9531_);
    return v_res_9533_;
}
pub unsafe fn l_IO_println(
    mut v_00_u03b1_9534_: *mut LeanObject,
    mut v_inst_9535_: *mut LeanObject,
    mut v_s_9536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9538_: *mut LeanObject = core::ptr::null_mut();
    v___x_9538_ = l_IO_println___redArg(v_inst_9535_, v_s_9536_);
    return v___x_9538_;
}
pub unsafe fn l_IO_println___boxed(
    mut v_00_u03b1_9539_: *mut LeanObject,
    mut v_inst_9540_: *mut LeanObject,
    mut v_s_9541_: *mut LeanObject,
    mut v_a_9542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9543_: *mut LeanObject = core::ptr::null_mut();
    v_res_9543_ = l_IO_println(v_00_u03b1_9539_, v_inst_9540_, v_s_9541_);
    return v_res_9543_;
}
pub unsafe fn l_IO_eprint___redArg(
    mut v_inst_9544_: *mut LeanObject,
    mut v_s_9545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_9548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9550_: *mut LeanObject = core::ptr::null_mut();
    v___x_9547_ = lean_get_stderr();
    v_putStr_9548_ = lean_ctor_get(v___x_9547_, 4);
    lean_inc_ref(v_putStr_9548_);
    lean_dec_ref(v___x_9547_);
    v___x_9549_ = lean_apply_1(v_inst_9544_, v_s_9545_);
    v___x_9550_ = lean_apply_2(v_putStr_9548_, v___x_9549_, lean_box(0));
    return v___x_9550_;
}
pub unsafe fn l_IO_eprint___redArg___boxed(
    mut v_inst_9551_: *mut LeanObject,
    mut v_s_9552_: *mut LeanObject,
    mut v_a_9553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9554_: *mut LeanObject = core::ptr::null_mut();
    v_res_9554_ = l_IO_eprint___redArg(v_inst_9551_, v_s_9552_);
    return v_res_9554_;
}
pub unsafe fn l_IO_eprint(
    mut v_00_u03b1_9555_: *mut LeanObject,
    mut v_inst_9556_: *mut LeanObject,
    mut v_s_9557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9559_: *mut LeanObject = core::ptr::null_mut();
    v___x_9559_ = l_IO_eprint___redArg(v_inst_9556_, v_s_9557_);
    return v___x_9559_;
}
pub unsafe fn l_IO_eprint___boxed(
    mut v_00_u03b1_9560_: *mut LeanObject,
    mut v_inst_9561_: *mut LeanObject,
    mut v_s_9562_: *mut LeanObject,
    mut v_a_9563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9564_: *mut LeanObject = core::ptr::null_mut();
    v_res_9564_ = l_IO_eprint(v_00_u03b1_9560_, v_inst_9561_, v_s_9562_);
    return v_res_9564_;
}
pub unsafe fn l_IO_eprintln___redArg(
    mut v_inst_9565_: *mut LeanObject,
    mut v_s_9566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9570_: u32 = 0;
    let mut v___x_9571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9572_: *mut LeanObject = core::ptr::null_mut();
    v___f_9568_ = l_IO_println___redArg___closed__0;
    v___x_9569_ = lean_apply_1(v_inst_9565_, v_s_9566_);
    v___x_9570_ = 10;
    v___x_9571_ = lean_string_push(v___x_9569_, v___x_9570_);
    v___x_9572_ = l_IO_eprint___redArg(v___f_9568_, v___x_9571_);
    return v___x_9572_;
}
pub unsafe fn l_IO_eprintln___redArg___boxed(
    mut v_inst_9573_: *mut LeanObject,
    mut v_s_9574_: *mut LeanObject,
    mut v_a_9575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9576_: *mut LeanObject = core::ptr::null_mut();
    v_res_9576_ = l_IO_eprintln___redArg(v_inst_9573_, v_s_9574_);
    return v_res_9576_;
}
pub unsafe fn l_IO_eprintln(
    mut v_00_u03b1_9577_: *mut LeanObject,
    mut v_inst_9578_: *mut LeanObject,
    mut v_s_9579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    v___x_9581_ = l_IO_eprintln___redArg(v_inst_9578_, v_s_9579_);
    return v___x_9581_;
}
pub unsafe fn l_IO_eprintln___boxed(
    mut v_00_u03b1_9582_: *mut LeanObject,
    mut v_inst_9583_: *mut LeanObject,
    mut v_s_9584_: *mut LeanObject,
    mut v_a_9585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9586_: *mut LeanObject = core::ptr::null_mut();
    v_res_9586_ = l_IO_eprintln(v_00_u03b1_9582_, v_inst_9583_, v_s_9584_);
    return v_res_9586_;
}
pub unsafe fn l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(
    mut v_s_9587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_9590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9591_: *mut LeanObject = core::ptr::null_mut();
    v___x_9589_ = lean_get_stderr();
    v_putStr_9590_ = lean_ctor_get(v___x_9589_, 4);
    lean_inc_ref(v_putStr_9590_);
    lean_dec_ref(v___x_9589_);
    v___x_9591_ = lean_apply_2(v_putStr_9590_, v_s_9587_, lean_box(0));
    return v___x_9591_;
}
pub unsafe fn l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(
    mut v_s_9592_: *mut LeanObject,
    mut v_a_9593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9594_: *mut LeanObject = core::ptr::null_mut();
    v_res_9594_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_9592_);
    return v_res_9594_;
}
pub unsafe fn lean_io_eprint(mut v_s_9595_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9597_: *mut LeanObject = core::ptr::null_mut();
    v___x_9597_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_9595_);
    return v___x_9597_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_eprintAux___boxed(
    mut v_s_9598_: *mut LeanObject,
    mut v_a_9599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9600_: *mut LeanObject = core::ptr::null_mut();
    v_res_9600_ = lean_io_eprint(v_s_9598_);
    return v_res_9600_;
}
pub unsafe fn l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(
    mut v_s_9601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9603_: u32 = 0;
    let mut v___x_9604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9605_: *mut LeanObject = core::ptr::null_mut();
    v___x_9603_ = 10;
    v___x_9604_ = lean_string_push(v_s_9601_, v___x_9603_);
    v___x_9605_ =
        l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_9604_);
    return v___x_9605_;
}
pub unsafe fn l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(
    mut v_s_9606_: *mut LeanObject,
    mut v_a_9607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9608_: *mut LeanObject = core::ptr::null_mut();
    v_res_9608_ =
        l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_9606_);
    return v_res_9608_;
}
pub unsafe fn lean_io_eprintln(mut v_s_9609_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9611_: *mut LeanObject = core::ptr::null_mut();
    v___x_9611_ =
        l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_9609_);
    return v___x_9611_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_eprintlnAux___boxed(
    mut v_s_9612_: *mut LeanObject,
    mut v_a_9613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9614_: *mut LeanObject = core::ptr::null_mut();
    v_res_9614_ = lean_io_eprintln(v_s_9612_);
    return v_res_9614_;
}
pub unsafe fn l_IO_appDir() -> *mut LeanObject {
    let mut v___x_9618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9622_: u8 = 0;
    let mut v___x_9623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9618_ = lean_io_app_path();
                if lean_obj_tag(v___x_9618_) == 0 {
                    v_a_9619_ = lean_ctor_get(v___x_9618_, 0);
                    v_isSharedCheck_9634_ = (!lean_is_exclusive(v___x_9618_)) as u8;
                    if v_isSharedCheck_9634_ == 0 {
                        v___x_9621_ = v___x_9618_;
                        v_isShared_9622_ = v_isSharedCheck_9634_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9619_);
                        lean_dec(v___x_9618_);
                        v___x_9621_ = lean_box(0);
                        v_isShared_9622_ = v_isSharedCheck_9634_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_9618_;
                }
            }
            1 => {
                lean_inc(v_a_9619_);
                v___x_9623_ = l_System_FilePath_parent(v_a_9619_);
                if lean_obj_tag(v___x_9623_) == 1 {
                    lean_del_object(v___x_9621_);
                    lean_dec(v_a_9619_);
                    v_val_9624_ = lean_ctor_get(v___x_9623_, 0);
                    lean_inc(v_val_9624_);
                    lean_dec_ref_known(v___x_9623_, 1);
                    v___x_9625_ = lean_io_realpath(v_val_9624_);
                    return v___x_9625_;
                } else {
                    lean_dec(v___x_9623_);
                    v___x_9626_ = l_IO_appDir___closed__0;
                    v___x_9627_ = lean_string_append(v___x_9626_, v_a_9619_);
                    lean_dec(v_a_9619_);
                    v___x_9628_ = l_IO_appDir___closed__1;
                    v___x_9629_ = lean_string_append(v___x_9627_, v___x_9628_);
                    v___x_9630_ = lean_mk_io_user_error(v___x_9629_);
                    if v_isShared_9622_ == 0 {
                        lean_ctor_set_tag(v___x_9621_, 1);
                        lean_ctor_set(v___x_9621_, 0, v___x_9630_);
                        v___x_9632_ = v___x_9621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9633_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9633_, 0, v___x_9630_);
                        v___x_9632_ = v_reuseFailAlloc_9633_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_appDir___boxed(mut v_a_9635_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9636_: *mut LeanObject = core::ptr::null_mut();
    v_res_9636_ = l_IO_appDir();
    return v_res_9636_;
}
pub unsafe fn l_IO_FS_createDirAll(mut v_p_9637_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9644_: u8 = 0;
    let mut v___x_9645_: u8 = 0;
    let mut v___x_9647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9653_: u8 = 0;
    let mut v___x_9654_: u8 = 0;
    let mut v___x_9655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9654_ = l_System_FilePath_isDir(v_p_9637_);
                if v___x_9654_ == 0 {
                    lean_inc_ref(v_p_9637_);
                    v___x_9655_ = l_System_FilePath_parent(v_p_9637_);
                    if lean_obj_tag(v___x_9655_) == 1 {
                        v_val_9656_ = lean_ctor_get(v___x_9655_, 0);
                        lean_inc(v_val_9656_);
                        lean_dec_ref_known(v___x_9655_, 1);
                        v___x_9657_ = l_IO_FS_createDirAll(v_val_9656_);
                        if lean_obj_tag(v___x_9657_) == 0 {
                            lean_dec_ref_known(v___x_9657_, 1);
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_p_9637_);
                            return v___x_9657_;
                        }
                    } else {
                        lean_dec(v___x_9655_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_9637_);
                    v___x_9658_ = lean_box(0);
                    v___x_9659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9659_, 0, v___x_9658_);
                    return v___x_9659_;
                }
            }
            1 => {
                v___x_9640_ = lean_io_create_dir(v_p_9637_);
                if lean_obj_tag(v___x_9640_) == 0 {
                    lean_dec_ref(v_p_9637_);
                    return v___x_9640_;
                } else {
                    v_a_9641_ = lean_ctor_get(v___x_9640_, 0);
                    v_isSharedCheck_9653_ = (!lean_is_exclusive(v___x_9640_)) as u8;
                    if v_isSharedCheck_9653_ == 0 {
                        v___x_9643_ = v___x_9640_;
                        v_isShared_9644_ = v_isSharedCheck_9653_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9641_);
                        lean_dec(v___x_9640_);
                        v___x_9643_ = lean_box(0);
                        v_isShared_9644_ = v_isSharedCheck_9653_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9645_ = l_System_FilePath_isDir(v_p_9637_);
                lean_dec_ref(v_p_9637_);
                if v___x_9645_ == 0 {
                    if v_isShared_9644_ == 0 {
                        v___x_9647_ = v___x_9643_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9648_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9648_, 0, v_a_9641_);
                        v___x_9647_ = v_reuseFailAlloc_9648_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_9641_);
                    v___x_9649_ = lean_box(0);
                    if v_isShared_9644_ == 0 {
                        lean_ctor_set_tag(v___x_9643_, 0);
                        lean_ctor_set(v___x_9643_, 0, v___x_9649_);
                        v___x_9651_ = v___x_9643_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9652_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9652_, 0, v___x_9649_);
                        v___x_9651_ = v_reuseFailAlloc_9652_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_9647_;
            }
            4 => {
                return v___x_9651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_createDirAll___boxed(
    mut v_p_9660_: *mut LeanObject,
    mut v_a_9661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9662_: *mut LeanObject = core::ptr::null_mut();
    v_res_9662_ = l_IO_FS_createDirAll(v_p_9660_);
    return v_res_9662_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(
    mut v_as_9663_: *mut LeanObject,
    mut v_sz_9664_: usize,
    mut v_i_9665_: usize,
    mut v_b_9666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9670_: usize = 0;
    let mut v___x_9671_: usize = 0;
    let mut v___x_9673_: u8 = 0;
    let mut v___x_9674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9679_: u8 = 0;
    let mut v___x_9680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9681_: u8 = 0;
    let mut v___x_9682_: u8 = 0;
    let mut v___x_9683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9688_: u8 = 0;
    let mut v___x_9690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9673_ = lean_usize_dec_lt(v_i_9665_, v_sz_9664_);
                if v___x_9673_ == 0 {
                    v___x_9674_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9674_, 0, v_b_9666_);
                    return v___x_9674_;
                } else {
                    v_a_9675_ = lean_array_uget_borrowed(v_as_9663_, v_i_9665_);
                    lean_inc(v_a_9675_);
                    v___x_9676_ = l_IO_FS_DirEntry_path(v_a_9675_);
                    v___x_9677_ = lean_io_symlink_metadata(v___x_9676_);
                    if lean_obj_tag(v___x_9677_) == 0 {
                        v_a_9678_ = lean_ctor_get(v___x_9677_, 0);
                        lean_inc(v_a_9678_);
                        lean_dec_ref_known(v___x_9677_, 1);
                        v_type_9679_ = lean_ctor_get_uint8(
                            v_a_9678_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
                        );
                        lean_dec(v_a_9678_);
                        v___x_9680_ = lean_box(0);
                        v___x_9681_ = 0;
                        v___x_9682_ = l_IO_FS_instBEqFileType_beq(v_type_9679_, v___x_9681_);
                        if v___x_9682_ == 0 {
                            v___x_9683_ = lean_io_remove_file(v___x_9676_);
                            lean_dec_ref(v___x_9676_);
                            if lean_obj_tag(v___x_9683_) == 0 {
                                lean_dec_ref_known(v___x_9683_, 1);
                                v_a_9669_ = v___x_9680_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_9683_;
                            }
                        } else {
                            v___x_9684_ = l_IO_FS_removeDirAll(v___x_9676_);
                            lean_dec_ref(v___x_9676_);
                            if lean_obj_tag(v___x_9684_) == 0 {
                                lean_dec_ref_known(v___x_9684_, 1);
                                v_a_9669_ = v___x_9680_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_9684_;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_9676_);
                        v_a_9685_ = lean_ctor_get(v___x_9677_, 0);
                        v_isSharedCheck_9692_ = (!lean_is_exclusive(v___x_9677_)) as u8;
                        if v_isSharedCheck_9692_ == 0 {
                            v___x_9687_ = v___x_9677_;
                            v_isShared_9688_ = v_isSharedCheck_9692_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_9685_);
                            lean_dec(v___x_9677_);
                            v___x_9687_ = lean_box(0);
                            v_isShared_9688_ = v_isSharedCheck_9692_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_9670_ = 1usize;
                v___x_9671_ = lean_usize_add(v_i_9665_, v___x_9670_);
                v_i_9665_ = v___x_9671_;
                v_b_9666_ = v_a_9669_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_9688_ == 0 {
                    v___x_9690_ = v___x_9687_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9691_, 0, v_a_9685_);
                    v___x_9690_ = v_reuseFailAlloc_9691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_removeDirAll(mut v_p_9693_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9698_: usize = 0;
    let mut v___x_9699_: usize = 0;
    let mut v___x_9700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9705_: u8 = 0;
    let mut v___x_9707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9695_ = lean_io_read_dir(v_p_9693_);
                if lean_obj_tag(v___x_9695_) == 0 {
                    v_a_9696_ = lean_ctor_get(v___x_9695_, 0);
                    lean_inc(v_a_9696_);
                    lean_dec_ref_known(v___x_9695_, 1);
                    v___x_9697_ = lean_box(0);
                    v_sz_9698_ = lean_array_size(v_a_9696_);
                    v___x_9699_ = 0usize;
                    v___x_9700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_9696_, v_sz_9698_, v___x_9699_, v___x_9697_);
                    lean_dec(v_a_9696_);
                    if lean_obj_tag(v___x_9700_) == 0 {
                        lean_dec_ref_known(v___x_9700_, 1);
                        v___x_9701_ = lean_io_remove_dir(v_p_9693_);
                        return v___x_9701_;
                    } else {
                        return v___x_9700_;
                    }
                } else {
                    v_a_9702_ = lean_ctor_get(v___x_9695_, 0);
                    v_isSharedCheck_9709_ = (!lean_is_exclusive(v___x_9695_)) as u8;
                    if v_isSharedCheck_9709_ == 0 {
                        v___x_9704_ = v___x_9695_;
                        v_isShared_9705_ = v_isSharedCheck_9709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9702_);
                        lean_dec(v___x_9695_);
                        v___x_9704_ = lean_box(0);
                        v_isShared_9705_ = v_isSharedCheck_9709_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9705_ == 0 {
                    v___x_9707_ = v___x_9704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9708_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9708_, 0, v_a_9702_);
                    v___x_9707_ = v_reuseFailAlloc_9708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_removeDirAll___boxed(
    mut v_p_9710_: *mut LeanObject,
    mut v_a_9711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9712_: *mut LeanObject = core::ptr::null_mut();
    v_res_9712_ = l_IO_FS_removeDirAll(v_p_9710_);
    lean_dec_ref(v_p_9710_);
    return v_res_9712_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(
    mut v_as_9713_: *mut LeanObject,
    mut v_sz_9714_: *mut LeanObject,
    mut v_i_9715_: *mut LeanObject,
    mut v_b_9716_: *mut LeanObject,
    mut v___y_9717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9718_: usize = 0;
    let mut v_i_boxed_9719_: usize = 0;
    let mut v_res_9720_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9718_ = lean_unbox_usize(v_sz_9714_);
    lean_dec(v_sz_9714_);
    v_i_boxed_9719_ = lean_unbox_usize(v_i_9715_);
    lean_dec(v_i_9715_);
    v_res_9720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_9713_, v_sz_boxed_9718_, v_i_boxed_9719_, v_b_9716_);
    lean_dec_ref(v_as_9713_);
    return v_res_9720_;
}
pub unsafe fn l_IO_FS_withTempFile___redArg___lam__2(
    mut v_toFunctor_9721_: *mut LeanObject,
    mut v_f_9722_: *mut LeanObject,
    mut v_inst_9723_: *mut LeanObject,
    mut v_inst_9724_: *mut LeanObject,
    mut v___f_9725_: *mut LeanObject,
    mut v_____x_9726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_9729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9735_: *mut LeanObject = core::ptr::null_mut();
    v_fst_9727_ = lean_ctor_get(v_____x_9726_, 0);
    lean_inc(v_fst_9727_);
    v_snd_9728_ = lean_ctor_get(v_____x_9726_, 1);
    lean_inc_n(v_snd_9728_, 2);
    lean_dec_ref(v_____x_9726_);
    v_map_9729_ = lean_ctor_get(v_toFunctor_9721_, 0);
    lean_inc(v_map_9729_);
    lean_dec_ref(v_toFunctor_9721_);
    v___x_9730_ = lean_apply_2(v_f_9722_, v_fst_9727_, v_snd_9728_);
    v___x_9731_ = lean_alloc_closure(l_IO_FS_removeFile___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9731_, 0, v_snd_9728_);
    v___x_9732_ = lean_apply_2(v_inst_9723_, lean_box(0), v___x_9731_);
    v___f_9733_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9733_, 0, v___x_9732_);
    v_y_9734_ = lean_apply_4(
        v_inst_9724_,
        lean_box(0),
        lean_box(0),
        v___x_9730_,
        v___f_9733_,
    );
    v___x_9735_ = lean_apply_4(
        v_map_9729_,
        lean_box(0),
        lean_box(0),
        v___f_9725_,
        v_y_9734_,
    );
    return v___x_9735_;
}
pub unsafe fn l_IO_FS_withTempFile___redArg(
    mut v_inst_9737_: *mut LeanObject,
    mut v_inst_9738_: *mut LeanObject,
    mut v_inst_9739_: *mut LeanObject,
    mut v_f_9740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9748_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9741_ = lean_ctor_get(v_inst_9737_, 0);
    lean_inc_ref(v_toApplicative_9741_);
    v_toBind_9742_ = lean_ctor_get(v_inst_9737_, 1);
    lean_inc(v_toBind_9742_);
    lean_dec_ref(v_inst_9737_);
    v_toFunctor_9743_ = lean_ctor_get(v_toApplicative_9741_, 0);
    lean_inc_ref(v_toFunctor_9743_);
    lean_dec_ref(v_toApplicative_9741_);
    v___f_9744_ = l_IO_withStdin___redArg___closed__0;
    v___x_9745_ = l_IO_FS_withTempFile___redArg___closed__0;
    lean_inc(v_inst_9739_);
    v___x_9746_ = lean_apply_2(v_inst_9739_, lean_box(0), v___x_9745_);
    v___f_9747_ = lean_alloc_closure(
        l_IO_FS_withTempFile___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_9747_, 0, v_toFunctor_9743_);
    lean_closure_set(v___f_9747_, 1, v_f_9740_);
    lean_closure_set(v___f_9747_, 2, v_inst_9739_);
    lean_closure_set(v___f_9747_, 3, v_inst_9738_);
    lean_closure_set(v___f_9747_, 4, v___f_9744_);
    v___x_9748_ = lean_apply_4(
        v_toBind_9742_,
        lean_box(0),
        lean_box(0),
        v___x_9746_,
        v___f_9747_,
    );
    return v___x_9748_;
}
pub unsafe fn l_IO_FS_withTempFile(
    mut v_m_9749_: *mut LeanObject,
    mut v_00_u03b1_9750_: *mut LeanObject,
    mut v_inst_9751_: *mut LeanObject,
    mut v_inst_9752_: *mut LeanObject,
    mut v_inst_9753_: *mut LeanObject,
    mut v_f_9754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9755_: *mut LeanObject = core::ptr::null_mut();
    v___x_9755_ =
        l_IO_FS_withTempFile___redArg(v_inst_9751_, v_inst_9752_, v_inst_9753_, v_f_9754_);
    return v___x_9755_;
}
pub unsafe fn l_IO_FS_withTempDir___redArg___lam__2(
    mut v_toFunctor_9756_: *mut LeanObject,
    mut v_f_9757_: *mut LeanObject,
    mut v_inst_9758_: *mut LeanObject,
    mut v_inst_9759_: *mut LeanObject,
    mut v___f_9760_: *mut LeanObject,
    mut v_path_9761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_9762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9768_: *mut LeanObject = core::ptr::null_mut();
    v_map_9762_ = lean_ctor_get(v_toFunctor_9756_, 0);
    lean_inc(v_map_9762_);
    lean_dec_ref(v_toFunctor_9756_);
    lean_inc_ref(v_path_9761_);
    v___x_9763_ = lean_apply_1(v_f_9757_, v_path_9761_);
    v___x_9764_ = lean_alloc_closure(l_IO_FS_removeDirAll___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_9764_, 0, v_path_9761_);
    v___x_9765_ = lean_apply_2(v_inst_9758_, lean_box(0), v___x_9764_);
    v___f_9766_ = lean_alloc_closure(
        l_IO_withStdin___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9766_, 0, v___x_9765_);
    v_y_9767_ = lean_apply_4(
        v_inst_9759_,
        lean_box(0),
        lean_box(0),
        v___x_9763_,
        v___f_9766_,
    );
    v___x_9768_ = lean_apply_4(
        v_map_9762_,
        lean_box(0),
        lean_box(0),
        v___f_9760_,
        v_y_9767_,
    );
    return v___x_9768_;
}
pub unsafe fn l_IO_FS_withTempDir___redArg(
    mut v_inst_9770_: *mut LeanObject,
    mut v_inst_9771_: *mut LeanObject,
    mut v_inst_9772_: *mut LeanObject,
    mut v_f_9773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9781_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9774_ = lean_ctor_get(v_inst_9770_, 0);
    lean_inc_ref(v_toApplicative_9774_);
    v_toBind_9775_ = lean_ctor_get(v_inst_9770_, 1);
    lean_inc(v_toBind_9775_);
    lean_dec_ref(v_inst_9770_);
    v_toFunctor_9776_ = lean_ctor_get(v_toApplicative_9774_, 0);
    lean_inc_ref(v_toFunctor_9776_);
    lean_dec_ref(v_toApplicative_9774_);
    v___f_9777_ = l_IO_withStdin___redArg___closed__0;
    v___x_9778_ = l_IO_FS_withTempDir___redArg___closed__0;
    lean_inc(v_inst_9772_);
    v___x_9779_ = lean_apply_2(v_inst_9772_, lean_box(0), v___x_9778_);
    v___f_9780_ = lean_alloc_closure(
        l_IO_FS_withTempDir___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_9780_, 0, v_toFunctor_9776_);
    lean_closure_set(v___f_9780_, 1, v_f_9773_);
    lean_closure_set(v___f_9780_, 2, v_inst_9772_);
    lean_closure_set(v___f_9780_, 3, v_inst_9771_);
    lean_closure_set(v___f_9780_, 4, v___f_9777_);
    v___x_9781_ = lean_apply_4(
        v_toBind_9775_,
        lean_box(0),
        lean_box(0),
        v___x_9779_,
        v___f_9780_,
    );
    return v___x_9781_;
}
pub unsafe fn l_IO_FS_withTempDir(
    mut v_m_9782_: *mut LeanObject,
    mut v_00_u03b1_9783_: *mut LeanObject,
    mut v_inst_9784_: *mut LeanObject,
    mut v_inst_9785_: *mut LeanObject,
    mut v_inst_9786_: *mut LeanObject,
    mut v_f_9787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9788_: *mut LeanObject = core::ptr::null_mut();
    v___x_9788_ = l_IO_FS_withTempDir___redArg(v_inst_9784_, v_inst_9785_, v_inst_9786_, v_f_9787_);
    return v___x_9788_;
}
pub unsafe fn l_IO_Process_getCurrentDir___boxed(
    mut v_a_00___x40___internal___hyg_9790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9791_: *mut LeanObject = core::ptr::null_mut();
    v_res_9791_ = lean_io_process_get_current_dir();
    return v_res_9791_;
}
pub unsafe fn l_IO_Process_setCurrentDir___boxed(
    mut v_path_9794_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9796_: *mut LeanObject = core::ptr::null_mut();
    v_res_9796_ = lean_io_process_set_current_dir(v_path_9794_);
    lean_dec_ref(v_path_9794_);
    return v_res_9796_;
}
pub unsafe fn l_IO_Process_getPID___boxed(
    mut v_a_00___x40___internal___hyg_9798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9799_: u32 = 0;
    let mut v_r_9800_: *mut LeanObject = core::ptr::null_mut();
    v_res_9799_ = lean_io_process_get_pid();
    v_r_9800_ = lean_box_uint32(v_res_9799_);
    return v_r_9800_;
}
pub unsafe fn l_IO_Process_Stdio_ctorIdx(mut v_x_9801_: u8) -> *mut LeanObject {
    match v_x_9801_ {
        0 => {
            let mut v___x_9802_: *mut LeanObject = core::ptr::null_mut();
            v___x_9802_ = lean_unsigned_to_nat(0);
            return v___x_9802_;
        }
        1 => {
            let mut v___x_9803_: *mut LeanObject = core::ptr::null_mut();
            v___x_9803_ = lean_unsigned_to_nat(1);
            return v___x_9803_;
        }
        _ => {
            let mut v___x_9804_: *mut LeanObject = core::ptr::null_mut();
            v___x_9804_ = lean_unsigned_to_nat(2);
            return v___x_9804_;
        }
    }
}
pub unsafe fn l_IO_Process_Stdio_ctorIdx___boxed(
    mut v_x_9805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_9806_: u8 = 0;
    let mut v_res_9807_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_9806_ = (lean_unbox(v_x_9805_) as u8);
    v_res_9807_ = l_IO_Process_Stdio_ctorIdx(v_x_boxed_9806_);
    return v_res_9807_;
}
pub unsafe fn l_IO_Process_Stdio_toCtorIdx(mut v_x_9808_: u8) -> *mut LeanObject {
    let mut v___x_9809_: *mut LeanObject = core::ptr::null_mut();
    v___x_9809_ = l_IO_Process_Stdio_ctorIdx(v_x_9808_);
    return v___x_9809_;
}
pub unsafe fn l_IO_Process_Stdio_toCtorIdx___boxed(
    mut v_x_9810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_9811_: u8 = 0;
    let mut v_res_9812_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_9811_ = (lean_unbox(v_x_9810_) as u8);
    v_res_9812_ = l_IO_Process_Stdio_toCtorIdx(v_x_4__boxed_9811_);
    return v_res_9812_;
}
pub unsafe fn l_IO_Process_Stdio_ctorElim___redArg(
    mut v_k_9813_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_9813_);
    return v_k_9813_;
}
pub unsafe fn l_IO_Process_Stdio_ctorElim___redArg___boxed(
    mut v_k_9814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9815_: *mut LeanObject = core::ptr::null_mut();
    v_res_9815_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_9814_);
    lean_dec(v_k_9814_);
    return v_res_9815_;
}
pub unsafe fn l_IO_Process_Stdio_ctorElim(
    mut v_motive_9816_: *mut LeanObject,
    mut v_ctorIdx_9817_: *mut LeanObject,
    mut v_t_9818_: u8,
    mut v_h_9819_: *mut LeanObject,
    mut v_k_9820_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_9820_);
    return v_k_9820_;
}
pub unsafe fn l_IO_Process_Stdio_ctorElim___boxed(
    mut v_motive_9821_: *mut LeanObject,
    mut v_ctorIdx_9822_: *mut LeanObject,
    mut v_t_9823_: *mut LeanObject,
    mut v_h_9824_: *mut LeanObject,
    mut v_k_9825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_9826_: u8 = 0;
    let mut v_res_9827_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_9826_ = (lean_unbox(v_t_9823_) as u8);
    v_res_9827_ = l_IO_Process_Stdio_ctorElim(
        v_motive_9821_,
        v_ctorIdx_9822_,
        v_t_boxed_9826_,
        v_h_9824_,
        v_k_9825_,
    );
    lean_dec(v_k_9825_);
    lean_dec(v_ctorIdx_9822_);
    return v_res_9827_;
}
pub unsafe fn l_IO_Process_Stdio_piped_elim___redArg(
    mut v_piped_9828_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_piped_9828_);
    return v_piped_9828_;
}
pub unsafe fn l_IO_Process_Stdio_piped_elim___redArg___boxed(
    mut v_piped_9829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9830_: *mut LeanObject = core::ptr::null_mut();
    v_res_9830_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_9829_);
    lean_dec(v_piped_9829_);
    return v_res_9830_;
}
pub unsafe fn l_IO_Process_Stdio_piped_elim(
    mut v_motive_9831_: *mut LeanObject,
    mut v_t_9832_: u8,
    mut v_h_9833_: *mut LeanObject,
    mut v_piped_9834_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_piped_9834_);
    return v_piped_9834_;
}
pub unsafe fn l_IO_Process_Stdio_piped_elim___boxed(
    mut v_motive_9835_: *mut LeanObject,
    mut v_t_9836_: *mut LeanObject,
    mut v_h_9837_: *mut LeanObject,
    mut v_piped_9838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_9839_: u8 = 0;
    let mut v_res_9840_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_9839_ = (lean_unbox(v_t_9836_) as u8);
    v_res_9840_ =
        l_IO_Process_Stdio_piped_elim(v_motive_9835_, v_t_boxed_9839_, v_h_9837_, v_piped_9838_);
    lean_dec(v_piped_9838_);
    return v_res_9840_;
}
pub unsafe fn l_IO_Process_Stdio_inherit_elim___redArg(
    mut v_inherit_9841_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inherit_9841_);
    return v_inherit_9841_;
}
pub unsafe fn l_IO_Process_Stdio_inherit_elim___redArg___boxed(
    mut v_inherit_9842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9843_: *mut LeanObject = core::ptr::null_mut();
    v_res_9843_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_9842_);
    lean_dec(v_inherit_9842_);
    return v_res_9843_;
}
pub unsafe fn l_IO_Process_Stdio_inherit_elim(
    mut v_motive_9844_: *mut LeanObject,
    mut v_t_9845_: u8,
    mut v_h_9846_: *mut LeanObject,
    mut v_inherit_9847_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inherit_9847_);
    return v_inherit_9847_;
}
pub unsafe fn l_IO_Process_Stdio_inherit_elim___boxed(
    mut v_motive_9848_: *mut LeanObject,
    mut v_t_9849_: *mut LeanObject,
    mut v_h_9850_: *mut LeanObject,
    mut v_inherit_9851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_9852_: u8 = 0;
    let mut v_res_9853_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_9852_ = (lean_unbox(v_t_9849_) as u8);
    v_res_9853_ = l_IO_Process_Stdio_inherit_elim(
        v_motive_9848_,
        v_t_boxed_9852_,
        v_h_9850_,
        v_inherit_9851_,
    );
    lean_dec(v_inherit_9851_);
    return v_res_9853_;
}
pub unsafe fn l_IO_Process_Stdio_null_elim___redArg(
    mut v_null_9854_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_null_9854_);
    return v_null_9854_;
}
pub unsafe fn l_IO_Process_Stdio_null_elim___redArg___boxed(
    mut v_null_9855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9856_: *mut LeanObject = core::ptr::null_mut();
    v_res_9856_ = l_IO_Process_Stdio_null_elim___redArg(v_null_9855_);
    lean_dec(v_null_9855_);
    return v_res_9856_;
}
pub unsafe fn l_IO_Process_Stdio_null_elim(
    mut v_motive_9857_: *mut LeanObject,
    mut v_t_9858_: u8,
    mut v_h_9859_: *mut LeanObject,
    mut v_null_9860_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_null_9860_);
    return v_null_9860_;
}
pub unsafe fn l_IO_Process_Stdio_null_elim___boxed(
    mut v_motive_9861_: *mut LeanObject,
    mut v_t_9862_: *mut LeanObject,
    mut v_h_9863_: *mut LeanObject,
    mut v_null_9864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_9865_: u8 = 0;
    let mut v_res_9866_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_9865_ = (lean_unbox(v_t_9862_) as u8);
    v_res_9866_ =
        l_IO_Process_Stdio_null_elim(v_motive_9861_, v_t_boxed_9865_, v_h_9863_, v_null_9864_);
    lean_dec(v_null_9864_);
    return v_res_9866_;
}
pub unsafe fn l_IO_Process_spawn___boxed(
    mut v_args_9869_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9871_: *mut LeanObject = core::ptr::null_mut();
    v_res_9871_ = lean_io_process_spawn(v_args_9869_);
    return v_res_9871_;
}
pub unsafe fn l_IO_Process_Child_wait___boxed(
    mut v_cfg_9875_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9876_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9878_: *mut LeanObject = core::ptr::null_mut();
    v_res_9878_ = lean_io_process_child_wait(v_cfg_9875_, v_a_00___x40___internal___hyg_9876_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9876_);
    lean_dec_ref(v_cfg_9875_);
    return v_res_9878_;
}
pub unsafe fn l_IO_Process_Child_tryWait___boxed(
    mut v_cfg_9882_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9883_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9885_: *mut LeanObject = core::ptr::null_mut();
    v_res_9885_ = lean_io_process_child_try_wait(v_cfg_9882_, v_a_00___x40___internal___hyg_9883_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9883_);
    lean_dec_ref(v_cfg_9882_);
    return v_res_9885_;
}
pub unsafe fn l_IO_Process_Child_kill___boxed(
    mut v_cfg_9889_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9890_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9892_: *mut LeanObject = core::ptr::null_mut();
    v_res_9892_ = lean_io_process_child_kill(v_cfg_9889_, v_a_00___x40___internal___hyg_9890_);
    lean_dec_ref(v_a_00___x40___internal___hyg_9890_);
    lean_dec_ref(v_cfg_9889_);
    return v_res_9892_;
}
pub unsafe fn l_IO_Process_Child_takeStdin___boxed(
    mut v_cfg_9896_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9897_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9899_: *mut LeanObject = core::ptr::null_mut();
    v_res_9899_ =
        lean_io_process_child_take_stdin(v_cfg_9896_, v_a_00___x40___internal___hyg_9897_);
    lean_dec_ref(v_cfg_9896_);
    return v_res_9899_;
}
pub unsafe fn l_IO_Process_Child_pid___boxed(
    mut v_cfg_9902_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9904_: u32 = 0;
    let mut v_r_9905_: *mut LeanObject = core::ptr::null_mut();
    v_res_9904_ = lean_io_process_child_pid(v_cfg_9902_, v_a_00___x40___internal___hyg_9903_);
    lean_dec_ref(v_cfg_9902_);
    v_r_9905_ = lean_box_uint32(v_res_9904_);
    return v_r_9905_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(
    mut v_e_9906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9911_: u8 = 0;
    let mut v___x_9912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9917_: u8 = 0;
    let mut v_a_9918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9921_: u8 = 0;
    let mut v___x_9923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_9906_) == 0 {
                    v_a_9908_ = lean_ctor_get(v_e_9906_, 0);
                    v_isSharedCheck_9917_ = (!lean_is_exclusive(v_e_9906_)) as u8;
                    if v_isSharedCheck_9917_ == 0 {
                        v___x_9910_ = v_e_9906_;
                        v_isShared_9911_ = v_isSharedCheck_9917_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9908_);
                        lean_dec(v_e_9906_);
                        v___x_9910_ = lean_box(0);
                        v_isShared_9911_ = v_isSharedCheck_9917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9918_ = lean_ctor_get(v_e_9906_, 0);
                    v_isSharedCheck_9925_ = (!lean_is_exclusive(v_e_9906_)) as u8;
                    if v_isSharedCheck_9925_ == 0 {
                        v___x_9920_ = v_e_9906_;
                        v_isShared_9921_ = v_isSharedCheck_9925_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9918_);
                        lean_dec(v_e_9906_);
                        v___x_9920_ = lean_box(0);
                        v_isShared_9921_ = v_isSharedCheck_9925_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9912_ = lean_io_error_to_string(v_a_9908_);
                v___x_9913_ = lean_mk_io_user_error(v___x_9912_);
                if v_isShared_9911_ == 0 {
                    lean_ctor_set_tag(v___x_9910_, 1);
                    lean_ctor_set(v___x_9910_, 0, v___x_9913_);
                    v___x_9915_ = v___x_9910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9916_, 0, v___x_9913_);
                    v___x_9915_ = v_reuseFailAlloc_9916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9915_;
            }
            3 => {
                if v_isShared_9921_ == 0 {
                    lean_ctor_set_tag(v___x_9920_, 0);
                    v___x_9923_ = v___x_9920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9924_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9924_, 0, v_a_9918_);
                    v___x_9923_ = v_reuseFailAlloc_9924_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(
    mut v_e_9926_: *mut LeanObject,
    mut v_a_9927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9928_: *mut LeanObject = core::ptr::null_mut();
    v_res_9928_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_9926_);
    return v_res_9928_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_Process_output_spec__0(
    mut v_00_u03b1_9929_: *mut LeanObject,
    mut v_e_9930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9932_: *mut LeanObject = core::ptr::null_mut();
    v___x_9932_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_9930_);
    return v___x_9932_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(
    mut v_00_u03b1_9933_: *mut LeanObject,
    mut v_e_9934_: *mut LeanObject,
    mut v_a_9935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9936_: *mut LeanObject = core::ptr::null_mut();
    v_res_9936_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_9933_, v_e_9934_);
    return v_res_9936_;
}
pub unsafe fn l_IO_Process_output___lam__0(mut v_stdout_9937_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9943_: u8 = 0;
    let mut v___x_9945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9947_: u8 = 0;
    let mut v_a_9948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9951_: u8 = 0;
    let mut v___x_9953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9939_ = l_IO_FS_Handle_readToEnd(v_stdout_9937_);
                if lean_obj_tag(v___x_9939_) == 0 {
                    v_a_9940_ = lean_ctor_get(v___x_9939_, 0);
                    v_isSharedCheck_9947_ = (!lean_is_exclusive(v___x_9939_)) as u8;
                    if v_isSharedCheck_9947_ == 0 {
                        v___x_9942_ = v___x_9939_;
                        v_isShared_9943_ = v_isSharedCheck_9947_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9940_);
                        lean_dec(v___x_9939_);
                        v___x_9942_ = lean_box(0);
                        v_isShared_9943_ = v_isSharedCheck_9947_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9948_ = lean_ctor_get(v___x_9939_, 0);
                    v_isSharedCheck_9955_ = (!lean_is_exclusive(v___x_9939_)) as u8;
                    if v_isSharedCheck_9955_ == 0 {
                        v___x_9950_ = v___x_9939_;
                        v_isShared_9951_ = v_isSharedCheck_9955_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9948_);
                        lean_dec(v___x_9939_);
                        v___x_9950_ = lean_box(0);
                        v_isShared_9951_ = v_isSharedCheck_9955_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9943_ == 0 {
                    lean_ctor_set_tag(v___x_9942_, 1);
                    v___x_9945_ = v___x_9942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9946_, 0, v_a_9940_);
                    v___x_9945_ = v_reuseFailAlloc_9946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9945_;
            }
            3 => {
                if v_isShared_9951_ == 0 {
                    lean_ctor_set_tag(v___x_9950_, 0);
                    v___x_9953_ = v___x_9950_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9954_, 0, v_a_9948_);
                    v___x_9953_ = v_reuseFailAlloc_9954_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_Process_output___lam__0___boxed(
    mut v_stdout_9956_: *mut LeanObject,
    mut v___y_9957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9958_: *mut LeanObject = core::ptr::null_mut();
    v_res_9958_ = l_IO_Process_output___lam__0(v_stdout_9956_);
    lean_dec(v_stdout_9956_);
    return v_res_9958_;
}
pub unsafe fn l_IO_Process_output(
    mut v_args_9964_: *mut LeanObject,
    mut v_input_x3f_9965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_child_9968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stdout_9969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_9970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9984_: u8 = 0;
    let mut v___x_9985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9986_: u32 = 0;
    let mut v___x_9988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9990_: u8 = 0;
    let mut v_a_9991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9994_: u8 = 0;
    let mut v___x_9996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9998_: u8 = 0;
    let mut v_a_9999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10002_: u8 = 0;
    let mut v___x_10004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10006_: u8 = 0;
    let mut v_a_10007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10010_: u8 = 0;
    let mut v___x_10012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10014_: u8 = 0;
    let mut v_val_10015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_10017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_10018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cwd_10019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_10020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritEnv_10021_: u8 = 0;
    let mut v_setsid_10022_: u8 = 0;
    let mut v___x_10024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10025_: u8 = 0;
    let mut v___x_10027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_10032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_10033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10039_: u8 = 0;
    let mut v___x_10041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10043_: u8 = 0;
    let mut v_a_10044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10047_: u8 = 0;
    let mut v___x_10049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10051_: u8 = 0;
    let mut v_a_10052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10055_: u8 = 0;
    let mut v___x_10057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10059_: u8 = 0;
    let mut v_a_10060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10063_: u8 = 0;
    let mut v___x_10065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10067_: u8 = 0;
    let mut v_reuseFailAlloc_10068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10069_: u8 = 0;
    let mut v_unused_10070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_10072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_10073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cwd_10074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_10075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritEnv_10076_: u8 = 0;
    let mut v_setsid_10077_: u8 = 0;
    let mut v___x_10079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10080_: u8 = 0;
    let mut v___x_10082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10088_: u8 = 0;
    let mut v___x_10090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10092_: u8 = 0;
    let mut v_reuseFailAlloc_10093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10094_: u8 = 0;
    let mut v_unused_10095_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_input_x3f_9965_) == 1 {
                    v_val_10015_ = lean_ctor_get(v_input_x3f_9965_, 0);
                    v___x_10016_ = l_IO_Process_output___closed__1;
                    v_cmd_10017_ = lean_ctor_get(v_args_9964_, 1);
                    v_args_10018_ = lean_ctor_get(v_args_9964_, 2);
                    v_cwd_10019_ = lean_ctor_get(v_args_9964_, 3);
                    v_env_10020_ = lean_ctor_get(v_args_9964_, 4);
                    v_inheritEnv_10021_ = lean_ctor_get_uint8(
                        v_args_9964_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_setsid_10022_ = lean_ctor_get_uint8(
                        v_args_9964_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_10069_ = (!lean_is_exclusive(v_args_9964_)) as u8;
                    if v_isSharedCheck_10069_ == 0 {
                        v_unused_10070_ = lean_ctor_get(v_args_9964_, 0);
                        lean_dec(v_unused_10070_);
                        v___x_10024_ = v_args_9964_;
                        v_isShared_10025_ = v_isSharedCheck_10069_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_env_10020_);
                        lean_inc(v_cwd_10019_);
                        lean_inc(v_args_10018_);
                        lean_inc(v_cmd_10017_);
                        lean_dec(v_args_9964_);
                        v___x_10024_ = lean_box(0);
                        v_isShared_10025_ = v_isSharedCheck_10069_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_10071_ = l_IO_Process_output___closed__0;
                    v_cmd_10072_ = lean_ctor_get(v_args_9964_, 1);
                    v_args_10073_ = lean_ctor_get(v_args_9964_, 2);
                    v_cwd_10074_ = lean_ctor_get(v_args_9964_, 3);
                    v_env_10075_ = lean_ctor_get(v_args_9964_, 4);
                    v_inheritEnv_10076_ = lean_ctor_get_uint8(
                        v_args_9964_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_setsid_10077_ = lean_ctor_get_uint8(
                        v_args_9964_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_10094_ = (!lean_is_exclusive(v_args_9964_)) as u8;
                    if v_isSharedCheck_10094_ == 0 {
                        v_unused_10095_ = lean_ctor_get(v_args_9964_, 0);
                        lean_dec(v_unused_10095_);
                        v___x_10079_ = v_args_9964_;
                        v_isShared_10080_ = v_isSharedCheck_10094_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_env_10075_);
                        lean_inc(v_cwd_10074_);
                        lean_inc(v_args_10073_);
                        lean_inc(v_cmd_10072_);
                        lean_dec(v_args_9964_);
                        v___x_10079_ = lean_box(0);
                        v_isShared_10080_ = v_isSharedCheck_10094_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v_stdout_9969_ = lean_ctor_get(v_child_9968_, 1);
                v_stderr_9970_ = lean_ctor_get(v_child_9968_, 2);
                lean_inc(v_stdout_9969_);
                v___f_9971_ = lean_alloc_closure(
                    l_IO_Process_output___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_9971_, 0, v_stdout_9969_);
                v___x_9972_ = lean_unsigned_to_nat(9);
                v___x_9973_ = lean_io_as_task(v___f_9971_, v___x_9972_);
                v___x_9974_ = l_IO_FS_Handle_readToEnd(v_stderr_9970_);
                if lean_obj_tag(v___x_9974_) == 0 {
                    v_a_9975_ = lean_ctor_get(v___x_9974_, 0);
                    lean_inc(v_a_9975_);
                    lean_dec_ref_known(v___x_9974_, 1);
                    v___x_9976_ = l_IO_Process_output___closed__0;
                    v___x_9977_ = lean_io_process_child_wait(v___x_9976_, v_child_9968_);
                    lean_dec_ref(v_child_9968_);
                    if lean_obj_tag(v___x_9977_) == 0 {
                        v_a_9978_ = lean_ctor_get(v___x_9977_, 0);
                        lean_inc(v_a_9978_);
                        lean_dec_ref_known(v___x_9977_, 1);
                        v___x_9979_ = lean_task_get_own(v___x_9973_);
                        v___x_9980_ =
                            l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_9979_);
                        if lean_obj_tag(v___x_9980_) == 0 {
                            v_a_9981_ = lean_ctor_get(v___x_9980_, 0);
                            v_isSharedCheck_9990_ = (!lean_is_exclusive(v___x_9980_)) as u8;
                            if v_isSharedCheck_9990_ == 0 {
                                v___x_9983_ = v___x_9980_;
                                v_isShared_9984_ = v_isSharedCheck_9990_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_9981_);
                                lean_dec(v___x_9980_);
                                v___x_9983_ = lean_box(0);
                                v_isShared_9984_ = v_isSharedCheck_9990_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_9978_);
                            lean_dec(v_a_9975_);
                            v_a_9991_ = lean_ctor_get(v___x_9980_, 0);
                            v_isSharedCheck_9998_ = (!lean_is_exclusive(v___x_9980_)) as u8;
                            if v_isSharedCheck_9998_ == 0 {
                                v___x_9993_ = v___x_9980_;
                                v_isShared_9994_ = v_isSharedCheck_9998_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_9991_);
                                lean_dec(v___x_9980_);
                                v___x_9993_ = lean_box(0);
                                v_isShared_9994_ = v_isSharedCheck_9998_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_9975_);
                        lean_dec_ref(v___x_9973_);
                        v_a_9999_ = lean_ctor_get(v___x_9977_, 0);
                        v_isSharedCheck_10006_ = (!lean_is_exclusive(v___x_9977_)) as u8;
                        if v_isSharedCheck_10006_ == 0 {
                            v___x_10001_ = v___x_9977_;
                            v_isShared_10002_ = v_isSharedCheck_10006_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9999_);
                            lean_dec(v___x_9977_);
                            v___x_10001_ = lean_box(0);
                            v_isShared_10002_ = v_isSharedCheck_10006_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_9973_);
                    lean_dec_ref(v_child_9968_);
                    v_a_10007_ = lean_ctor_get(v___x_9974_, 0);
                    v_isSharedCheck_10014_ = (!lean_is_exclusive(v___x_9974_)) as u8;
                    if v_isSharedCheck_10014_ == 0 {
                        v___x_10009_ = v___x_9974_;
                        v_isShared_10010_ = v_isSharedCheck_10014_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_10007_);
                        lean_dec(v___x_9974_);
                        v___x_10009_ = lean_box(0);
                        v_isShared_10010_ = v_isSharedCheck_10014_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9985_ = lean_alloc_ctor(0, 2, (4) as u32);
                lean_ctor_set(v___x_9985_, 0, v_a_9981_);
                lean_ctor_set(v___x_9985_, 1, v_a_9975_);
                v___x_9986_ = lean_unbox_uint32(v_a_9978_);
                lean_dec(v_a_9978_);
                lean_ctor_set_uint32(
                    v___x_9985_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_9986_,
                );
                if v_isShared_9984_ == 0 {
                    lean_ctor_set(v___x_9983_, 0, v___x_9985_);
                    v___x_9988_ = v___x_9983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9989_, 0, v___x_9985_);
                    v___x_9988_ = v_reuseFailAlloc_9989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9988_;
            }
            4 => {
                if v_isShared_9994_ == 0 {
                    v___x_9996_ = v___x_9993_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9997_, 0, v_a_9991_);
                    v___x_9996_ = v_reuseFailAlloc_9997_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9996_;
            }
            6 => {
                if v_isShared_10002_ == 0 {
                    v___x_10004_ = v___x_10001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_10005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10005_, 0, v_a_9999_);
                    v___x_10004_ = v_reuseFailAlloc_10005_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_10004_;
            }
            8 => {
                if v_isShared_10010_ == 0 {
                    v___x_10012_ = v___x_10009_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_10013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10013_, 0, v_a_10007_);
                    v___x_10012_ = v_reuseFailAlloc_10013_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_10012_;
            }
            10 => {
                if v_isShared_10025_ == 0 {
                    lean_ctor_set(v___x_10024_, 0, v___x_10016_);
                    v___x_10027_ = v___x_10024_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_10068_ = lean_alloc_ctor(0, 5, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10068_, 0, v___x_10016_);
                    lean_ctor_set(v_reuseFailAlloc_10068_, 1, v_cmd_10017_);
                    lean_ctor_set(v_reuseFailAlloc_10068_, 2, v_args_10018_);
                    lean_ctor_set(v_reuseFailAlloc_10068_, 3, v_cwd_10019_);
                    lean_ctor_set(v_reuseFailAlloc_10068_, 4, v_env_10020_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_10068_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_inheritEnv_10021_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_10068_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v_setsid_10022_,
                    );
                    v___x_10027_ = v_reuseFailAlloc_10068_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_10028_ = lean_io_process_spawn(v___x_10027_);
                if lean_obj_tag(v___x_10028_) == 0 {
                    v_a_10029_ = lean_ctor_get(v___x_10028_, 0);
                    lean_inc(v_a_10029_);
                    lean_dec_ref_known(v___x_10028_, 1);
                    v___x_10030_ = lean_io_process_child_take_stdin(v___x_10016_, v_a_10029_);
                    if lean_obj_tag(v___x_10030_) == 0 {
                        v_a_10031_ = lean_ctor_get(v___x_10030_, 0);
                        lean_inc(v_a_10031_);
                        lean_dec_ref_known(v___x_10030_, 1);
                        v_fst_10032_ = lean_ctor_get(v_a_10031_, 0);
                        lean_inc(v_fst_10032_);
                        v_snd_10033_ = lean_ctor_get(v_a_10031_, 1);
                        lean_inc(v_snd_10033_);
                        lean_dec(v_a_10031_);
                        v___x_10034_ = lean_io_prim_handle_put_str(v_fst_10032_, v_val_10015_);
                        if lean_obj_tag(v___x_10034_) == 0 {
                            lean_dec_ref_known(v___x_10034_, 1);
                            v___x_10035_ = lean_io_prim_handle_flush(v_fst_10032_);
                            lean_dec(v_fst_10032_);
                            if lean_obj_tag(v___x_10035_) == 0 {
                                lean_dec_ref_known(v___x_10035_, 1);
                                v_child_9968_ = v_snd_10033_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_snd_10033_);
                                v_a_10036_ = lean_ctor_get(v___x_10035_, 0);
                                v_isSharedCheck_10043_ = (!lean_is_exclusive(v___x_10035_)) as u8;
                                if v_isSharedCheck_10043_ == 0 {
                                    v___x_10038_ = v___x_10035_;
                                    v_isShared_10039_ = v_isSharedCheck_10043_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_10036_);
                                    lean_dec(v___x_10035_);
                                    v___x_10038_ = lean_box(0);
                                    v_isShared_10039_ = v_isSharedCheck_10043_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_10033_);
                            lean_dec(v_fst_10032_);
                            v_a_10044_ = lean_ctor_get(v___x_10034_, 0);
                            v_isSharedCheck_10051_ = (!lean_is_exclusive(v___x_10034_)) as u8;
                            if v_isSharedCheck_10051_ == 0 {
                                v___x_10046_ = v___x_10034_;
                                v_isShared_10047_ = v_isSharedCheck_10051_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_10044_);
                                lean_dec(v___x_10034_);
                                v___x_10046_ = lean_box(0);
                                v_isShared_10047_ = v_isSharedCheck_10051_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        v_a_10052_ = lean_ctor_get(v___x_10030_, 0);
                        v_isSharedCheck_10059_ = (!lean_is_exclusive(v___x_10030_)) as u8;
                        if v_isSharedCheck_10059_ == 0 {
                            v___x_10054_ = v___x_10030_;
                            v_isShared_10055_ = v_isSharedCheck_10059_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_10052_);
                            lean_dec(v___x_10030_);
                            v___x_10054_ = lean_box(0);
                            v_isShared_10055_ = v_isSharedCheck_10059_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    v_a_10060_ = lean_ctor_get(v___x_10028_, 0);
                    v_isSharedCheck_10067_ = (!lean_is_exclusive(v___x_10028_)) as u8;
                    if v_isSharedCheck_10067_ == 0 {
                        v___x_10062_ = v___x_10028_;
                        v_isShared_10063_ = v_isSharedCheck_10067_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_10060_);
                        lean_dec(v___x_10028_);
                        v___x_10062_ = lean_box(0);
                        v_isShared_10063_ = v_isSharedCheck_10067_;
                        state = 18;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_10039_ == 0 {
                    v___x_10041_ = v___x_10038_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_10042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10042_, 0, v_a_10036_);
                    v___x_10041_ = v_reuseFailAlloc_10042_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_10041_;
            }
            14 => {
                if v_isShared_10047_ == 0 {
                    v___x_10049_ = v___x_10046_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_10050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10050_, 0, v_a_10044_);
                    v___x_10049_ = v_reuseFailAlloc_10050_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_10049_;
            }
            16 => {
                if v_isShared_10055_ == 0 {
                    v___x_10057_ = v___x_10054_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_10058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10058_, 0, v_a_10052_);
                    v___x_10057_ = v_reuseFailAlloc_10058_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_10057_;
            }
            18 => {
                if v_isShared_10063_ == 0 {
                    v___x_10065_ = v___x_10062_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_10066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10066_, 0, v_a_10060_);
                    v___x_10065_ = v_reuseFailAlloc_10066_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_10065_;
            }
            20 => {
                if v_isShared_10080_ == 0 {
                    lean_ctor_set(v___x_10079_, 0, v___x_10071_);
                    v___x_10082_ = v___x_10079_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_10093_ = lean_alloc_ctor(0, 5, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10093_, 0, v___x_10071_);
                    lean_ctor_set(v_reuseFailAlloc_10093_, 1, v_cmd_10072_);
                    lean_ctor_set(v_reuseFailAlloc_10093_, 2, v_args_10073_);
                    lean_ctor_set(v_reuseFailAlloc_10093_, 3, v_cwd_10074_);
                    lean_ctor_set(v_reuseFailAlloc_10093_, 4, v_env_10075_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_10093_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_inheritEnv_10076_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_10093_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v_setsid_10077_,
                    );
                    v___x_10082_ = v_reuseFailAlloc_10093_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_10083_ = lean_io_process_spawn(v___x_10082_);
                if lean_obj_tag(v___x_10083_) == 0 {
                    v_a_10084_ = lean_ctor_get(v___x_10083_, 0);
                    lean_inc(v_a_10084_);
                    lean_dec_ref_known(v___x_10083_, 1);
                    v_child_9968_ = v_a_10084_;
                    state = 1;
                    continue;
                } else {
                    v_a_10085_ = lean_ctor_get(v___x_10083_, 0);
                    v_isSharedCheck_10092_ = (!lean_is_exclusive(v___x_10083_)) as u8;
                    if v_isSharedCheck_10092_ == 0 {
                        v___x_10087_ = v___x_10083_;
                        v_isShared_10088_ = v_isSharedCheck_10092_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_10085_);
                        lean_dec(v___x_10083_);
                        v___x_10087_ = lean_box(0);
                        v_isShared_10088_ = v_isSharedCheck_10092_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_10088_ == 0 {
                    v___x_10090_ = v___x_10087_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_10091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10091_, 0, v_a_10085_);
                    v___x_10090_ = v_reuseFailAlloc_10091_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_10090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_Process_output___boxed(
    mut v_args_10096_: *mut LeanObject,
    mut v_input_x3f_10097_: *mut LeanObject,
    mut v_a_10098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10099_: *mut LeanObject = core::ptr::null_mut();
    v_res_10099_ = l_IO_Process_output(v_args_10096_, v_input_x3f_10097_);
    lean_dec(v_input_x3f_10097_);
    return v_res_10099_;
}
pub unsafe fn l_IO_Process_run(
    mut v_args_10103_: *mut LeanObject,
    mut v_input_x3f_10104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10110_: u8 = 0;
    let mut v_exitCode_10111_: u32 = 0;
    let mut v_stdout_10112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_10113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10114_: u32 = 0;
    let mut v___x_10115_: u8 = 0;
    let mut v_cmd_10116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10134_: u8 = 0;
    let mut v_a_10135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10138_: u8 = 0;
    let mut v___x_10140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_args_10103_);
                v___x_10106_ = l_IO_Process_output(v_args_10103_, v_input_x3f_10104_);
                if lean_obj_tag(v___x_10106_) == 0 {
                    v_a_10107_ = lean_ctor_get(v___x_10106_, 0);
                    v_isSharedCheck_10134_ = (!lean_is_exclusive(v___x_10106_)) as u8;
                    if v_isSharedCheck_10134_ == 0 {
                        v___x_10109_ = v___x_10106_;
                        v_isShared_10110_ = v_isSharedCheck_10134_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10107_);
                        lean_dec(v___x_10106_);
                        v___x_10109_ = lean_box(0);
                        v_isShared_10110_ = v_isSharedCheck_10134_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_10103_);
                    v_a_10135_ = lean_ctor_get(v___x_10106_, 0);
                    v_isSharedCheck_10142_ = (!lean_is_exclusive(v___x_10106_)) as u8;
                    if v_isSharedCheck_10142_ == 0 {
                        v___x_10137_ = v___x_10106_;
                        v_isShared_10138_ = v_isSharedCheck_10142_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10135_);
                        lean_dec(v___x_10106_);
                        v___x_10137_ = lean_box(0);
                        v_isShared_10138_ = v_isSharedCheck_10142_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_exitCode_10111_ = lean_ctor_get_uint32(
                    v_a_10107_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_stdout_10112_ = lean_ctor_get(v_a_10107_, 0);
                lean_inc_ref(v_stdout_10112_);
                v_stderr_10113_ = lean_ctor_get(v_a_10107_, 1);
                lean_inc_ref(v_stderr_10113_);
                lean_dec(v_a_10107_);
                v___x_10114_ = 0;
                v___x_10115_ = lean_uint32_dec_eq(v_exitCode_10111_, v___x_10114_);
                if v___x_10115_ == 0 {
                    lean_dec_ref(v_stdout_10112_);
                    v_cmd_10116_ = lean_ctor_get(v_args_10103_, 1);
                    lean_inc_ref(v_cmd_10116_);
                    lean_dec_ref(v_args_10103_);
                    v___x_10117_ = l_IO_Process_run___closed__0;
                    v___x_10118_ = lean_string_append(v___x_10117_, v_cmd_10116_);
                    lean_dec_ref(v_cmd_10116_);
                    v___x_10119_ = l_IO_Process_run___closed__1;
                    v___x_10120_ = lean_string_append(v___x_10118_, v___x_10119_);
                    v___x_10121_ = lean_uint32_to_nat(v_exitCode_10111_);
                    v___x_10122_ = l_Nat_reprFast(v___x_10121_);
                    v___x_10123_ = lean_string_append(v___x_10120_, v___x_10122_);
                    lean_dec_ref(v___x_10122_);
                    v___x_10124_ = l_IO_Process_run___closed__2;
                    v___x_10125_ = lean_string_append(v___x_10123_, v___x_10124_);
                    v___x_10126_ = lean_string_append(v___x_10125_, v_stderr_10113_);
                    lean_dec_ref(v_stderr_10113_);
                    v___x_10127_ = lean_mk_io_user_error(v___x_10126_);
                    if v_isShared_10110_ == 0 {
                        lean_ctor_set_tag(v___x_10109_, 1);
                        lean_ctor_set(v___x_10109_, 0, v___x_10127_);
                        v___x_10129_ = v___x_10109_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_10130_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10130_, 0, v___x_10127_);
                        v___x_10129_ = v_reuseFailAlloc_10130_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_stderr_10113_);
                    lean_dec_ref(v_args_10103_);
                    if v_isShared_10110_ == 0 {
                        lean_ctor_set(v___x_10109_, 0, v_stdout_10112_);
                        v___x_10132_ = v___x_10109_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_10133_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10133_, 0, v_stdout_10112_);
                        v___x_10132_ = v_reuseFailAlloc_10133_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_10129_;
            }
            3 => {
                return v___x_10132_;
            }
            4 => {
                if v_isShared_10138_ == 0 {
                    v___x_10140_ = v___x_10137_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10141_, 0, v_a_10135_);
                    v___x_10140_ = v_reuseFailAlloc_10141_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_Process_run___boxed(
    mut v_args_10143_: *mut LeanObject,
    mut v_input_x3f_10144_: *mut LeanObject,
    mut v_a_10145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10146_: *mut LeanObject = core::ptr::null_mut();
    v_res_10146_ = l_IO_Process_run(v_args_10143_, v_input_x3f_10144_);
    lean_dec(v_input_x3f_10144_);
    return v_res_10146_;
}
pub unsafe fn l_IO_Process_exit___boxed(
    mut v_00_u03b1_10150_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10151_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_10153_: u8 = 0;
    let mut v_res_10154_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_10153_ =
        (lean_unbox(v_a_00___x40___internal___hyg_10151_) as u8);
    v_res_10154_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_10153_);
    return v_res_10154_;
}
pub unsafe fn l_IO_Process_forceExit___boxed(
    mut v_00_u03b1_10158_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10159_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_10161_: u8 = 0;
    let mut v_res_10162_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_10161_ =
        (lean_unbox(v_a_00___x40___internal___hyg_10159_) as u8);
    v_res_10162_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_10161_);
    return v_res_10162_;
}
pub unsafe fn l_IO_getTID___boxed(
    mut v_a_00___x40___internal___hyg_10164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10165_: u64 = 0;
    let mut v_r_10166_: *mut LeanObject = core::ptr::null_mut();
    v_res_10165_ = lean_io_get_tid();
    v_r_10166_ = lean_box_uint64(v_res_10165_);
    return v_r_10166_;
}
pub unsafe fn l_IO_AccessRight_flags(mut v_acc_10167_: *mut LeanObject) -> u32 {
    let mut v___y_10169_: u32 = 0;
    let mut v___y_10170_: u32 = 0;
    let mut v___y_10171_: u32 = 0;
    let mut v___x_10172_: u32 = 0;
    let mut v___x_10173_: u32 = 0;
    let mut v_read_10174_: u8 = 0;
    let mut v_write_10175_: u8 = 0;
    let mut v_execution_10176_: u8 = 0;
    let mut v___y_10178_: u32 = 0;
    let mut v___y_10179_: u32 = 0;
    let mut v___x_10180_: u32 = 0;
    let mut v___x_10181_: u32 = 0;
    let mut v___y_10183_: u32 = 0;
    let mut v___x_10184_: u32 = 0;
    let mut v___x_10185_: u32 = 0;
    let mut v___x_10186_: u32 = 0;
    let mut v___x_10187_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_read_10174_ = lean_ctor_get_uint8(v_acc_10167_, 0 as u32);
                v_write_10175_ = lean_ctor_get_uint8(v_acc_10167_, 1 as u32);
                v_execution_10176_ = lean_ctor_get_uint8(v_acc_10167_, 2 as u32);
                if v_read_10174_ == 0 {
                    v___x_10186_ = 0;
                    v___y_10183_ = v___x_10186_;
                    state = 3;
                    continue;
                } else {
                    v___x_10187_ = 4;
                    v___y_10183_ = v___x_10187_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_10172_ = lean_uint32_lor(v___y_10169_, v___y_10171_);
                v___x_10173_ = lean_uint32_lor(v___y_10170_, v___x_10172_);
                return v___x_10173_;
            }
            2 => {
                if v_execution_10176_ == 0 {
                    v___x_10180_ = 0;
                    v___y_10169_ = v___y_10179_;
                    v___y_10170_ = v___y_10178_;
                    v___y_10171_ = v___x_10180_;
                    state = 1;
                    continue;
                } else {
                    v___x_10181_ = 1;
                    v___y_10169_ = v___y_10179_;
                    v___y_10170_ = v___y_10178_;
                    v___y_10171_ = v___x_10181_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_write_10175_ == 0 {
                    v___x_10184_ = 0;
                    v___y_10178_ = v___y_10183_;
                    v___y_10179_ = v___x_10184_;
                    state = 2;
                    continue;
                } else {
                    v___x_10185_ = 2;
                    v___y_10178_ = v___y_10183_;
                    v___y_10179_ = v___x_10185_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AccessRight_flags___boxed(mut v_acc_10188_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_10189_: u32 = 0;
    let mut v_r_10190_: *mut LeanObject = core::ptr::null_mut();
    v_res_10189_ = l_IO_AccessRight_flags(v_acc_10188_);
    lean_dec_ref(v_acc_10188_);
    v_r_10190_ = lean_box_uint32(v_res_10189_);
    return v_r_10190_;
}
pub unsafe fn l_IO_FileRight_flags(mut v_acc_10191_: *mut LeanObject) -> u32 {
    let mut v_user_10192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_group_10193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_other_10194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10195_: u32 = 0;
    let mut v___x_10196_: u32 = 0;
    let mut v_u_10197_: u32 = 0;
    let mut v___x_10198_: u32 = 0;
    let mut v___x_10199_: u32 = 0;
    let mut v_g_10200_: u32 = 0;
    let mut v_o_10201_: u32 = 0;
    let mut v___x_10202_: u32 = 0;
    let mut v___x_10203_: u32 = 0;
    v_user_10192_ = lean_ctor_get(v_acc_10191_, 0);
    v_group_10193_ = lean_ctor_get(v_acc_10191_, 1);
    v_other_10194_ = lean_ctor_get(v_acc_10191_, 2);
    v___x_10195_ = l_IO_AccessRight_flags(v_user_10192_);
    v___x_10196_ = 6;
    v_u_10197_ = lean_uint32_shift_left(v___x_10195_, v___x_10196_);
    v___x_10198_ = l_IO_AccessRight_flags(v_group_10193_);
    v___x_10199_ = 3;
    v_g_10200_ = lean_uint32_shift_left(v___x_10198_, v___x_10199_);
    v_o_10201_ = l_IO_AccessRight_flags(v_other_10194_);
    v___x_10202_ = lean_uint32_lor(v_g_10200_, v_o_10201_);
    v___x_10203_ = lean_uint32_lor(v_u_10197_, v___x_10202_);
    return v___x_10203_;
}
pub unsafe fn l_IO_FileRight_flags___boxed(mut v_acc_10204_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_10205_: u32 = 0;
    let mut v_r_10206_: *mut LeanObject = core::ptr::null_mut();
    v_res_10205_ = l_IO_FileRight_flags(v_acc_10204_);
    lean_dec_ref(v_acc_10204_);
    v_r_10206_ = lean_box_uint32(v_res_10205_);
    return v_r_10206_;
}
pub unsafe fn l_IO_Prim_setAccessRights___boxed(
    mut v_filename_10210_: *mut LeanObject,
    mut v_mode_10211_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_10213_: u32 = 0;
    let mut v_res_10214_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_10213_ = lean_unbox_uint32(v_mode_10211_);
    lean_dec(v_mode_10211_);
    v_res_10214_ = lean_chmod(v_filename_10210_, v_mode_boxed_10213_);
    lean_dec_ref(v_filename_10210_);
    return v_res_10214_;
}
pub unsafe fn l_IO_setAccessRights(
    mut v_filename_10215_: *mut LeanObject,
    mut v_mode_10216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10218_: u32 = 0;
    let mut v___x_10219_: *mut LeanObject = core::ptr::null_mut();
    v___x_10218_ = l_IO_FileRight_flags(v_mode_10216_);
    v___x_10219_ = lean_chmod(v_filename_10215_, v___x_10218_);
    return v___x_10219_;
}
pub unsafe fn l_IO_setAccessRights___boxed(
    mut v_filename_10220_: *mut LeanObject,
    mut v_mode_10221_: *mut LeanObject,
    mut v_a_10222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10223_: *mut LeanObject = core::ptr::null_mut();
    v_res_10223_ = l_IO_setAccessRights(v_filename_10220_, v_mode_10221_);
    lean_dec_ref(v_mode_10221_);
    lean_dec_ref(v_filename_10220_);
    return v_res_10223_;
}
pub unsafe fn l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(
    mut v_00_u03b1_10224_: *mut LeanObject,
    mut v_mx_10225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10227_: *mut LeanObject = core::ptr::null_mut();
    v___x_10227_ = lean_apply_1(v_mx_10225_, lean_box(0));
    return v___x_10227_;
}
pub unsafe fn l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(
    mut v_00_u03b1_10228_: *mut LeanObject,
    mut v_mx_10229_: *mut LeanObject,
    mut v_s_10230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10231_: *mut LeanObject = core::ptr::null_mut();
    v_res_10231_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_10228_, v_mx_10229_);
    return v_res_10231_;
}
pub unsafe fn l_IO_mkRef___redArg(mut v_a_10234_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10236_: *mut LeanObject = core::ptr::null_mut();
    v___x_10236_ = lean_st_mk_ref(v_a_10234_);
    return v___x_10236_;
}
pub unsafe fn l_IO_mkRef___redArg___boxed(
    mut v_a_10237_: *mut LeanObject,
    mut v_a_10238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10239_: *mut LeanObject = core::ptr::null_mut();
    v_res_10239_ = l_IO_mkRef___redArg(v_a_10237_);
    return v_res_10239_;
}
pub unsafe fn l_IO_mkRef(
    mut v_00_u03b1_10240_: *mut LeanObject,
    mut v_a_10241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10243_: *mut LeanObject = core::ptr::null_mut();
    v___x_10243_ = lean_st_mk_ref(v_a_10241_);
    return v___x_10243_;
}
pub unsafe fn l_IO_mkRef___boxed(
    mut v_00_u03b1_10244_: *mut LeanObject,
    mut v_a_10245_: *mut LeanObject,
    mut v_a_10246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10247_: *mut LeanObject = core::ptr::null_mut();
    v_res_10247_ = l_IO_mkRef(v_00_u03b1_10244_, v_a_10245_);
    return v_res_10247_;
}
pub unsafe fn lean_stream_of_handle(mut v_h_10248_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10255_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_h_10248_, 5);
    v___x_10249_ = lean_alloc_closure(l_IO_FS_Handle_flush___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_10249_, 0, v_h_10248_);
    v___x_10250_ = lean_alloc_closure(l_IO_FS_Handle_read___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___x_10250_, 0, v_h_10248_);
    v___x_10251_ = lean_alloc_closure(l_IO_FS_Handle_write___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___x_10251_, 0, v_h_10248_);
    v___x_10252_ = lean_alloc_closure(
        l_IO_FS_Handle_getLine___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_10252_, 0, v_h_10248_);
    v___x_10253_ = lean_alloc_closure(
        l_IO_FS_Handle_putStr___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_10253_, 0, v_h_10248_);
    v___x_10254_ = lean_alloc_closure(l_IO_FS_Handle_isTty___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_10254_, 0, v_h_10248_);
    v___x_10255_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_10255_, 0, v___x_10249_);
    lean_ctor_set(v___x_10255_, 1, v___x_10250_);
    lean_ctor_set(v___x_10255_, 2, v___x_10251_);
    lean_ctor_set(v___x_10255_, 3, v___x_10252_);
    lean_ctor_set(v___x_10255_, 4, v___x_10253_);
    lean_ctor_set(v___x_10255_, 5, v___x_10254_);
    return v___x_10255_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__0(
    mut v_r_10256_: *mut LeanObject,
    mut v_n_10257_: usize,
) -> *mut LeanObject {
    let mut v___x_10259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_10261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10264_: u8 = 0;
    let mut v___x_10265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10259_ = lean_st_ref_take(v_r_10256_);
                v_data_10260_ = lean_ctor_get(v___x_10259_, 0);
                v_pos_10261_ = lean_ctor_get(v___x_10259_, 1);
                v_isSharedCheck_10275_ = (!lean_is_exclusive(v___x_10259_)) as u8;
                if v_isSharedCheck_10275_ == 0 {
                    v___x_10263_ = v___x_10259_;
                    v_isShared_10264_ = v_isSharedCheck_10275_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_10261_);
                    lean_inc(v_data_10260_);
                    lean_dec(v___x_10259_);
                    v___x_10263_ = lean_box(0);
                    v_isShared_10264_ = v_isSharedCheck_10275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10265_ = lean_usize_to_nat(v_n_10257_);
                v___x_10266_ = lean_nat_add(v_pos_10261_, v___x_10265_);
                lean_dec(v___x_10265_);
                lean_inc(v_pos_10261_);
                v_data_10267_ = l_ByteArray_extract(v_data_10260_, v_pos_10261_, v___x_10266_);
                lean_dec(v___x_10266_);
                v___x_10268_ = lean_byte_array_size(v_data_10267_);
                v___x_10269_ = lean_nat_add(v_pos_10261_, v___x_10268_);
                lean_dec(v_pos_10261_);
                if v_isShared_10264_ == 0 {
                    lean_ctor_set(v___x_10263_, 1, v___x_10269_);
                    v___x_10271_ = v___x_10263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10274_, 0, v_data_10260_);
                    lean_ctor_set(v_reuseFailAlloc_10274_, 1, v___x_10269_);
                    v___x_10271_ = v_reuseFailAlloc_10274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10272_ = lean_st_ref_set(v_r_10256_, v___x_10271_);
                v___x_10273_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10273_, 0, v_data_10267_);
                return v___x_10273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__0___boxed(
    mut v_r_10276_: *mut LeanObject,
    mut v_n_10277_: *mut LeanObject,
    mut v___y_10278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_10279_: usize = 0;
    let mut v_res_10280_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_10279_ = lean_unbox_usize(v_n_10277_);
    lean_dec(v_n_10277_);
    v_res_10280_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_10276_, v_n_boxed_10279_);
    lean_dec(v_r_10276_);
    return v_res_10280_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__1(
    mut v_r_10281_: *mut LeanObject,
    mut v_data_10282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_10286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10289_: u8 = 0;
    let mut v___x_10290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10292_: u8 = 0;
    let mut v___x_10293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10284_ = lean_st_ref_take(v_r_10281_);
                v_data_10285_ = lean_ctor_get(v___x_10284_, 0);
                v_pos_10286_ = lean_ctor_get(v___x_10284_, 1);
                v_isSharedCheck_10300_ = (!lean_is_exclusive(v___x_10284_)) as u8;
                if v_isSharedCheck_10300_ == 0 {
                    v___x_10288_ = v___x_10284_;
                    v_isShared_10289_ = v_isSharedCheck_10300_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_10286_);
                    lean_inc(v_data_10285_);
                    lean_dec(v___x_10284_);
                    v___x_10288_ = lean_box(0);
                    v_isShared_10289_ = v_isSharedCheck_10300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10290_ = lean_unsigned_to_nat(0);
                v___x_10291_ = lean_byte_array_size(v_data_10282_);
                v___x_10292_ = 0;
                lean_inc(v_pos_10286_);
                v___x_10293_ = lean_byte_array_copy_slice(
                    v_data_10282_,
                    v___x_10290_,
                    v_data_10285_,
                    v_pos_10286_,
                    v___x_10291_,
                    v___x_10292_,
                );
                v___x_10294_ = lean_nat_add(v_pos_10286_, v___x_10291_);
                lean_dec(v_pos_10286_);
                if v_isShared_10289_ == 0 {
                    lean_ctor_set(v___x_10288_, 1, v___x_10294_);
                    lean_ctor_set(v___x_10288_, 0, v___x_10293_);
                    v___x_10296_ = v___x_10288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10299_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10299_, 0, v___x_10293_);
                    lean_ctor_set(v_reuseFailAlloc_10299_, 1, v___x_10294_);
                    v___x_10296_ = v_reuseFailAlloc_10299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10297_ = lean_st_ref_set(v_r_10281_, v___x_10296_);
                v___x_10298_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10298_, 0, v___x_10297_);
                return v___x_10298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__1___boxed(
    mut v_r_10301_: *mut LeanObject,
    mut v_data_10302_: *mut LeanObject,
    mut v___y_10303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10304_: *mut LeanObject = core::ptr::null_mut();
    v_res_10304_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_10301_, v_data_10302_);
    lean_dec_ref(v_data_10302_);
    lean_dec(v_r_10301_);
    return v_res_10304_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__2(
    mut v_r_10305_: *mut LeanObject,
    mut v_s_10306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_10310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10313_: u8 = 0;
    let mut v_data_10314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10317_: u8 = 0;
    let mut v___x_10318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10308_ = lean_st_ref_take(v_r_10305_);
                v_data_10309_ = lean_ctor_get(v___x_10308_, 0);
                v_pos_10310_ = lean_ctor_get(v___x_10308_, 1);
                v_isSharedCheck_10325_ = (!lean_is_exclusive(v___x_10308_)) as u8;
                if v_isSharedCheck_10325_ == 0 {
                    v___x_10312_ = v___x_10308_;
                    v_isShared_10313_ = v_isSharedCheck_10325_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_10310_);
                    lean_inc(v_data_10309_);
                    lean_dec(v___x_10308_);
                    v___x_10312_ = lean_box(0);
                    v_isShared_10313_ = v_isSharedCheck_10325_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_10314_ = lean_string_to_utf8(v_s_10306_);
                v___x_10315_ = lean_unsigned_to_nat(0);
                v___x_10316_ = lean_byte_array_size(v_data_10314_);
                v___x_10317_ = 0;
                lean_inc(v_pos_10310_);
                v___x_10318_ = lean_byte_array_copy_slice(
                    v_data_10314_,
                    v___x_10315_,
                    v_data_10309_,
                    v_pos_10310_,
                    v___x_10316_,
                    v___x_10317_,
                );
                lean_dec_ref(v_data_10314_);
                v___x_10319_ = lean_nat_add(v_pos_10310_, v___x_10316_);
                lean_dec(v_pos_10310_);
                if v_isShared_10313_ == 0 {
                    lean_ctor_set(v___x_10312_, 1, v___x_10319_);
                    lean_ctor_set(v___x_10312_, 0, v___x_10318_);
                    v___x_10321_ = v___x_10312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10324_, 0, v___x_10318_);
                    lean_ctor_set(v_reuseFailAlloc_10324_, 1, v___x_10319_);
                    v___x_10321_ = v_reuseFailAlloc_10324_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10322_ = lean_st_ref_set(v_r_10305_, v___x_10321_);
                v___x_10323_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10323_, 0, v___x_10322_);
                return v___x_10323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__2___boxed(
    mut v_r_10326_: *mut LeanObject,
    mut v_s_10327_: *mut LeanObject,
    mut v___y_10328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10329_: *mut LeanObject = core::ptr::null_mut();
    v_res_10329_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_10326_, v_s_10327_);
    lean_dec_ref(v_s_10327_);
    lean_dec(v_r_10326_);
    return v_res_10329_;
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(
    mut v_a_10330_: *mut LeanObject,
    mut v_i_10331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10333_: u8 = 0;
    let mut v___x_10334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10339_: u8 = 0;
    let mut v___x_10340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10341_: u8 = 0;
    let mut v___x_10342_: u8 = 0;
    let mut v___x_10343_: u8 = 0;
    let mut v___x_10344_: u8 = 0;
    let mut v___x_10345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10338_ = lean_byte_array_size(v_a_10330_);
                v___x_10339_ = lean_nat_dec_lt(v_i_10331_, v___x_10338_);
                if v___x_10339_ == 0 {
                    lean_dec(v_i_10331_);
                    v___x_10340_ = lean_box(0);
                    return v___x_10340_;
                } else {
                    v___x_10341_ = lean_byte_array_fget(v_a_10330_, v_i_10331_);
                    v___x_10342_ = 0;
                    v___x_10343_ = lean_uint8_dec_eq(v___x_10341_, v___x_10342_);
                    if v___x_10343_ == 0 {
                        v___x_10344_ = 10;
                        v___x_10345_ = lean_uint8_dec_eq(v___x_10341_, v___x_10344_);
                        v___y_10333_ = v___x_10345_;
                        state = 1;
                        continue;
                    } else {
                        v___y_10333_ = v___x_10343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_10333_ == 0 {
                    v___x_10334_ = lean_unsigned_to_nat(1);
                    v___x_10335_ = lean_nat_add(v_i_10331_, v___x_10334_);
                    lean_dec(v_i_10331_);
                    v_i_10331_ = v___x_10335_;
                    state = 0;
                    continue;
                } else {
                    v___x_10337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10337_, 0, v_i_10331_);
                    return v___x_10337_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(
    mut v_a_10346_: *mut LeanObject,
    mut v_i_10347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10348_: *mut LeanObject = core::ptr::null_mut();
    v_res_10348_ =
        l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_10346_, v_i_10347_);
    lean_dec_ref(v_a_10346_);
    return v_res_10348_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__3(mut v_r_10352_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_10356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10359_: u8 = 0;
    let mut v___y_10361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10366_: u8 = 0;
    let mut v___x_10367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10375_: u8 = 0;
    let mut v___x_10376_: u8 = 0;
    let mut v___x_10377_: u8 = 0;
    let mut v___x_10378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10354_ = lean_st_ref_take(v_r_10352_);
                v_data_10355_ = lean_ctor_get(v___x_10354_, 0);
                v_pos_10356_ = lean_ctor_get(v___x_10354_, 1);
                v_isSharedCheck_10380_ = (!lean_is_exclusive(v___x_10354_)) as u8;
                if v_isSharedCheck_10380_ == 0 {
                    v___x_10358_ = v___x_10354_;
                    v_isShared_10359_ = v_isSharedCheck_10380_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_10356_);
                    lean_inc(v_data_10355_);
                    lean_dec(v___x_10354_);
                    v___x_10358_ = lean_box(0);
                    v_isShared_10359_ = v_isSharedCheck_10380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_pos_10356_);
                v___x_10372_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(
                    v_data_10355_,
                    v_pos_10356_,
                );
                if lean_obj_tag(v___x_10372_) == 0 {
                    v___x_10373_ = lean_byte_array_size(v_data_10355_);
                    v___y_10361_ = v___x_10373_;
                    state = 2;
                    continue;
                } else {
                    v_val_10374_ = lean_ctor_get(v___x_10372_, 0);
                    lean_inc(v_val_10374_);
                    lean_dec_ref_known(v___x_10372_, 1);
                    v___x_10375_ = lean_byte_array_get(v_data_10355_, v_val_10374_);
                    v___x_10376_ = 0;
                    v___x_10377_ = lean_uint8_dec_eq(v___x_10375_, v___x_10376_);
                    if v___x_10377_ == 0 {
                        v___x_10378_ = lean_unsigned_to_nat(1);
                        v___x_10379_ = lean_nat_add(v_val_10374_, v___x_10378_);
                        lean_dec(v_val_10374_);
                        v___y_10361_ = v___x_10379_;
                        state = 2;
                        continue;
                    } else {
                        v___y_10361_ = v_val_10374_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_10362_ = l_ByteArray_extract(v_data_10355_, v_pos_10356_, v___y_10361_);
                if v_isShared_10359_ == 0 {
                    lean_ctor_set(v___x_10358_, 1, v___y_10361_);
                    v___x_10364_ = v___x_10358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10371_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10371_, 0, v_data_10355_);
                    lean_ctor_set(v_reuseFailAlloc_10371_, 1, v___y_10361_);
                    v___x_10364_ = v_reuseFailAlloc_10371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_10365_ = lean_st_ref_set(v_r_10352_, v___x_10364_);
                v___x_10366_ = lean_string_validate_utf8(v___x_10362_);
                if v___x_10366_ == 0 {
                    lean_dec_ref(v___x_10362_);
                    v___x_10367_ = l_IO_FS_Stream_ofBuffer___lam__3___closed__1;
                    v___x_10368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10368_, 0, v___x_10367_);
                    return v___x_10368_;
                } else {
                    v___x_10369_ = lean_string_from_utf8_unchecked(v___x_10362_);
                    v___x_10370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10370_, 0, v___x_10369_);
                    return v___x_10370_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__3___boxed(
    mut v_r_10381_: *mut LeanObject,
    mut v___y_10382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10383_: *mut LeanObject = core::ptr::null_mut();
    v_res_10383_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_10381_);
    lean_dec(v_r_10381_);
    return v_res_10383_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__4(
    mut v___x_10384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10386_: *mut LeanObject = core::ptr::null_mut();
    v___x_10386_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10386_, 0, v___x_10384_);
    return v___x_10386_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer___lam__4___boxed(
    mut v___x_10387_: *mut LeanObject,
    mut v___y_10388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10389_: *mut LeanObject = core::ptr::null_mut();
    v_res_10389_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_10387_);
    return v_res_10389_;
}
pub unsafe fn l_IO_FS_Stream_ofBuffer(mut v_r_10392_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_10393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10399_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_r_10392_, 3);
    v___f_10393_ = lean_alloc_closure(
        l_IO_FS_Stream_ofBuffer___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_10393_, 0, v_r_10392_);
    v___f_10394_ = lean_alloc_closure(
        l_IO_FS_Stream_ofBuffer___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_10394_, 0, v_r_10392_);
    v___f_10395_ = lean_alloc_closure(
        l_IO_FS_Stream_ofBuffer___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_10395_, 0, v_r_10392_);
    v___f_10396_ = lean_alloc_closure(
        l_IO_FS_Stream_ofBuffer___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_10396_, 0, v_r_10392_);
    v___f_10397_ = l_IO_FS_Stream_ofBuffer___closed__0;
    v___f_10398_ = l_IO_FS_instInhabitedStream_default___closed__5;
    v___x_10399_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_10399_, 0, v___f_10397_);
    lean_ctor_set(v___x_10399_, 1, v___f_10393_);
    lean_ctor_set(v___x_10399_, 2, v___f_10394_);
    lean_ctor_set(v___x_10399_, 3, v___f_10396_);
    lean_ctor_set(v___x_10399_, 4, v___f_10395_);
    lean_ctor_set(v___x_10399_, 5, v___f_10398_);
    return v___x_10399_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(
    mut v_s_10402_: *mut LeanObject,
    mut v_acc_10403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_read_10405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10411_: u8 = 0;
    let mut v___x_10412_: u8 = 0;
    let mut v___x_10413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_read_10405_ = lean_ctor_get(v_s_10402_, 1);
                v___x_10406_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1;
                lean_inc_ref(v_read_10405_);
                v___x_10407_ = lean_apply_2(v_read_10405_, v___x_10406_, lean_box(0));
                if lean_obj_tag(v___x_10407_) == 0 {
                    v_a_10408_ = lean_ctor_get(v___x_10407_, 0);
                    v_isSharedCheck_10421_ = (!lean_is_exclusive(v___x_10407_)) as u8;
                    if v_isSharedCheck_10421_ == 0 {
                        v___x_10410_ = v___x_10407_;
                        v_isShared_10411_ = v_isSharedCheck_10421_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10408_);
                        lean_dec(v___x_10407_);
                        v___x_10410_ = lean_box(0);
                        v_isShared_10411_ = v_isSharedCheck_10421_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_acc_10403_);
                    lean_dec_ref(v_s_10402_);
                    return v___x_10407_;
                }
            }
            1 => {
                v___x_10412_ = l_ByteArray_isEmpty(v_a_10408_);
                if v___x_10412_ == 0 {
                    lean_del_object(v___x_10410_);
                    v___x_10413_ = lean_unsigned_to_nat(0);
                    v___x_10414_ = lean_byte_array_size(v_acc_10403_);
                    v___x_10415_ = lean_byte_array_size(v_a_10408_);
                    v___x_10416_ = lean_byte_array_copy_slice(
                        v_a_10408_,
                        v___x_10413_,
                        v_acc_10403_,
                        v___x_10414_,
                        v___x_10415_,
                        v___x_10412_,
                    );
                    lean_dec(v_a_10408_);
                    v_acc_10403_ = v___x_10416_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_10408_);
                    lean_dec_ref(v_s_10402_);
                    if v_isShared_10411_ == 0 {
                        lean_ctor_set(v___x_10410_, 0, v_acc_10403_);
                        v___x_10419_ = v___x_10410_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_10420_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10420_, 0, v_acc_10403_);
                        v___x_10419_ = v_reuseFailAlloc_10420_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_10419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(
    mut v_s_10422_: *mut LeanObject,
    mut v_acc_10423_: *mut LeanObject,
    mut v_a_10424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10425_: *mut LeanObject = core::ptr::null_mut();
    v_res_10425_ =
        l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_10422_, v_acc_10423_);
    return v_res_10425_;
}
pub unsafe fn l_IO_FS_Stream_readBinToEndInto(
    mut v_s_10426_: *mut LeanObject,
    mut v_buf_10427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10429_: *mut LeanObject = core::ptr::null_mut();
    v___x_10429_ =
        l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_10426_, v_buf_10427_);
    return v___x_10429_;
}
pub unsafe fn l_IO_FS_Stream_readBinToEndInto___boxed(
    mut v_s_10430_: *mut LeanObject,
    mut v_buf_10431_: *mut LeanObject,
    mut v_a_10432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10433_: *mut LeanObject = core::ptr::null_mut();
    v_res_10433_ = l_IO_FS_Stream_readBinToEndInto(v_s_10430_, v_buf_10431_);
    return v_res_10433_;
}
pub unsafe fn l_IO_FS_Stream_readBinToEnd(mut v_s_10434_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10437_: *mut LeanObject = core::ptr::null_mut();
    v___x_10436_ = l_ByteArray_empty;
    v___x_10437_ =
        l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_10434_, v___x_10436_);
    return v___x_10437_;
}
pub unsafe fn l_IO_FS_Stream_readBinToEnd___boxed(
    mut v_s_10438_: *mut LeanObject,
    mut v_a_10439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10440_: *mut LeanObject = core::ptr::null_mut();
    v_res_10440_ = l_IO_FS_Stream_readBinToEnd(v_s_10438_);
    return v_res_10440_;
}
pub unsafe fn l_IO_FS_Stream_readToEnd(mut v_s_10444_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10450_: u8 = 0;
    let mut v___x_10451_: u8 = 0;
    let mut v___x_10452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10460_: u8 = 0;
    let mut v_a_10461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10464_: u8 = 0;
    let mut v___x_10466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10446_ = l_IO_FS_Stream_readBinToEnd(v_s_10444_);
                if lean_obj_tag(v___x_10446_) == 0 {
                    v_a_10447_ = lean_ctor_get(v___x_10446_, 0);
                    v_isSharedCheck_10460_ = (!lean_is_exclusive(v___x_10446_)) as u8;
                    if v_isSharedCheck_10460_ == 0 {
                        v___x_10449_ = v___x_10446_;
                        v_isShared_10450_ = v_isSharedCheck_10460_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10447_);
                        lean_dec(v___x_10446_);
                        v___x_10449_ = lean_box(0);
                        v_isShared_10450_ = v_isSharedCheck_10460_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10461_ = lean_ctor_get(v___x_10446_, 0);
                    v_isSharedCheck_10468_ = (!lean_is_exclusive(v___x_10446_)) as u8;
                    if v_isSharedCheck_10468_ == 0 {
                        v___x_10463_ = v___x_10446_;
                        v_isShared_10464_ = v_isSharedCheck_10468_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10461_);
                        lean_dec(v___x_10446_);
                        v___x_10463_ = lean_box(0);
                        v_isShared_10464_ = v_isSharedCheck_10468_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10451_ = lean_string_validate_utf8(v_a_10447_);
                if v___x_10451_ == 0 {
                    lean_dec(v_a_10447_);
                    v___x_10452_ = l_IO_FS_Stream_readToEnd___closed__1;
                    if v_isShared_10450_ == 0 {
                        lean_ctor_set_tag(v___x_10449_, 1);
                        lean_ctor_set(v___x_10449_, 0, v___x_10452_);
                        v___x_10454_ = v___x_10449_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_10455_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10455_, 0, v___x_10452_);
                        v___x_10454_ = v_reuseFailAlloc_10455_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_10456_ = lean_string_from_utf8_unchecked(v_a_10447_);
                    if v_isShared_10450_ == 0 {
                        lean_ctor_set(v___x_10449_, 0, v___x_10456_);
                        v___x_10458_ = v___x_10449_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_10459_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10459_, 0, v___x_10456_);
                        v___x_10458_ = v_reuseFailAlloc_10459_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_10454_;
            }
            3 => {
                return v___x_10458_;
            }
            4 => {
                if v_isShared_10464_ == 0 {
                    v___x_10466_ = v___x_10463_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10467_, 0, v_a_10461_);
                    v___x_10466_ = v_reuseFailAlloc_10467_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readToEnd___boxed(
    mut v_s_10469_: *mut LeanObject,
    mut v_a_10470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10471_: *mut LeanObject = core::ptr::null_mut();
    v_res_10471_ = l_IO_FS_Stream_readToEnd(v_s_10469_);
    return v_res_10471_;
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Stream_lines_read(
    mut v_s_10472_: *mut LeanObject,
    mut v_lines_10473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getLine_10475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10480_: u8 = 0;
    let mut v___y_10482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10489_: u32 = 0;
    let mut v___x_10490_: u32 = 0;
    let mut v___x_10491_: u8 = 0;
    let mut v___x_10492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10497_: u32 = 0;
    let mut v___x_10498_: u32 = 0;
    let mut v___x_10499_: u8 = 0;
    let mut v___x_10500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10513_: u32 = 0;
    let mut v_val_10514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10516_: u32 = 0;
    let mut v_val_10517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10518_: u32 = 0;
    let mut v___x_10519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10521_: u8 = 0;
    let mut v___x_10522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10524_: u32 = 0;
    let mut v_val_10525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10527_: u32 = 0;
    let mut v_val_10528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10529_: u32 = 0;
    let mut v___x_10530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10531_: u8 = 0;
    let mut v_a_10532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10535_: u8 = 0;
    let mut v___x_10537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getLine_10475_ = lean_ctor_get(v_s_10472_, 3);
                lean_inc_ref(v_getLine_10475_);
                v___x_10476_ = lean_apply_1(v_getLine_10475_, lean_box(0));
                if lean_obj_tag(v___x_10476_) == 0 {
                    v_a_10477_ = lean_ctor_get(v___x_10476_, 0);
                    v_isSharedCheck_10531_ = (!lean_is_exclusive(v___x_10476_)) as u8;
                    if v_isSharedCheck_10531_ == 0 {
                        v___x_10479_ = v___x_10476_;
                        v_isShared_10480_ = v_isSharedCheck_10531_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10477_);
                        lean_dec(v___x_10476_);
                        v___x_10479_ = lean_box(0);
                        v_isShared_10480_ = v_isSharedCheck_10531_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lines_10473_);
                    lean_dec_ref(v_s_10472_);
                    v_a_10532_ = lean_ctor_get(v___x_10476_, 0);
                    v_isSharedCheck_10539_ = (!lean_is_exclusive(v___x_10476_)) as u8;
                    if v_isSharedCheck_10539_ == 0 {
                        v___x_10534_ = v___x_10476_;
                        v_isShared_10535_ = v_isSharedCheck_10539_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_10532_);
                        lean_dec(v___x_10476_);
                        v___x_10534_ = lean_box(0);
                        v_isShared_10535_ = v_isSharedCheck_10539_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10519_ = lean_string_utf8_byte_size(v_a_10477_);
                v___x_10520_ = lean_unsigned_to_nat(0);
                v___x_10521_ = lean_nat_dec_eq(v___x_10519_, v___x_10520_);
                if v___x_10521_ == 0 {
                    lean_inc(v_a_10477_);
                    v___x_10522_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_10522_, 0, v_a_10477_);
                    lean_ctor_set(v___x_10522_, 1, v___x_10520_);
                    lean_ctor_set(v___x_10522_, 2, v___x_10519_);
                    v___x_10523_ = l_String_Slice_Pos_prev_x3f(v___x_10522_, v___x_10519_);
                    if lean_obj_tag(v___x_10523_) == 0 {
                        lean_dec_ref_known(v___x_10522_, 3);
                        v___x_10524_ = 65;
                        v___y_10497_ = v___x_10524_;
                        state = 4;
                        continue;
                    } else {
                        v_val_10525_ = lean_ctor_get(v___x_10523_, 0);
                        lean_inc(v_val_10525_);
                        lean_dec_ref_known(v___x_10523_, 1);
                        v___x_10526_ = l_String_Slice_Pos_get_x3f(v___x_10522_, v_val_10525_);
                        lean_dec(v_val_10525_);
                        lean_dec_ref_known(v___x_10522_, 3);
                        if lean_obj_tag(v___x_10526_) == 0 {
                            v___x_10527_ = 65;
                            v___y_10497_ = v___x_10527_;
                            state = 4;
                            continue;
                        } else {
                            v_val_10528_ = lean_ctor_get(v___x_10526_, 0);
                            lean_inc(v_val_10528_);
                            lean_dec_ref_known(v___x_10526_, 1);
                            v___x_10529_ = lean_unbox_uint32(v_val_10528_);
                            lean_dec(v_val_10528_);
                            v___y_10497_ = v___x_10529_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_10479_);
                    lean_dec(v_a_10477_);
                    lean_dec_ref(v_s_10472_);
                    v___x_10530_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10530_, 0, v_lines_10473_);
                    return v___x_10530_;
                }
            }
            2 => {
                v___x_10483_ = lean_array_push(v_lines_10473_, v___y_10482_);
                v_lines_10473_ = v___x_10483_;
                state = 0;
                continue;
            }
            3 => {
                v___x_10490_ = 13;
                v___x_10491_ = lean_uint32_dec_eq(v___y_10489_, v___x_10490_);
                if v___x_10491_ == 0 {
                    lean_dec(v___y_10488_);
                    lean_dec(v___y_10487_);
                    v___y_10482_ = v___y_10486_;
                    state = 2;
                    continue;
                } else {
                    v___x_10492_ = lean_string_utf8_byte_size(v___y_10486_);
                    lean_inc(v___y_10487_);
                    lean_inc_ref(v___y_10486_);
                    v___x_10493_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_10493_, 0, v___y_10486_);
                    lean_ctor_set(v___x_10493_, 1, v___y_10487_);
                    lean_ctor_set(v___x_10493_, 2, v___x_10492_);
                    v___x_10494_ =
                        l_String_Slice_Pos_prevn(v___x_10493_, v___x_10492_, v___y_10488_);
                    lean_dec_ref_known(v___x_10493_, 3);
                    v___x_10495_ =
                        lean_string_utf8_extract(v___y_10486_, v___y_10487_, v___x_10494_);
                    lean_dec(v___x_10494_);
                    lean_dec(v___y_10487_);
                    lean_dec_ref(v___y_10486_);
                    v___y_10482_ = v___x_10495_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_10498_ = 10;
                v___x_10499_ = lean_uint32_dec_eq(v___y_10497_, v___x_10498_);
                if v___x_10499_ == 0 {
                    lean_dec_ref(v_s_10472_);
                    v___x_10500_ = lean_array_push(v_lines_10473_, v_a_10477_);
                    if v_isShared_10480_ == 0 {
                        lean_ctor_set(v___x_10479_, 0, v___x_10500_);
                        v___x_10502_ = v___x_10479_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_10503_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10503_, 0, v___x_10500_);
                        v___x_10502_ = v_reuseFailAlloc_10503_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_10479_);
                    v___x_10504_ = lean_unsigned_to_nat(1);
                    v___x_10505_ = lean_unsigned_to_nat(0);
                    v___x_10506_ = lean_string_utf8_byte_size(v_a_10477_);
                    lean_inc(v_a_10477_);
                    v___x_10507_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_10507_, 0, v_a_10477_);
                    lean_ctor_set(v___x_10507_, 1, v___x_10505_);
                    lean_ctor_set(v___x_10507_, 2, v___x_10506_);
                    v___x_10508_ =
                        l_String_Slice_Pos_prevn(v___x_10507_, v___x_10506_, v___x_10504_);
                    lean_dec_ref_known(v___x_10507_, 3);
                    v___x_10509_ = lean_string_utf8_extract(v_a_10477_, v___x_10505_, v___x_10508_);
                    lean_dec(v___x_10508_);
                    lean_dec(v_a_10477_);
                    v___x_10510_ = lean_string_utf8_byte_size(v___x_10509_);
                    lean_inc_ref(v___x_10509_);
                    v___x_10511_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_10511_, 0, v___x_10509_);
                    lean_ctor_set(v___x_10511_, 1, v___x_10505_);
                    lean_ctor_set(v___x_10511_, 2, v___x_10510_);
                    v___x_10512_ = l_String_Slice_Pos_prev_x3f(v___x_10511_, v___x_10510_);
                    if lean_obj_tag(v___x_10512_) == 0 {
                        lean_dec_ref_known(v___x_10511_, 3);
                        v___x_10513_ = 65;
                        v___y_10486_ = v___x_10509_;
                        v___y_10487_ = v___x_10505_;
                        v___y_10488_ = v___x_10504_;
                        v___y_10489_ = v___x_10513_;
                        state = 3;
                        continue;
                    } else {
                        v_val_10514_ = lean_ctor_get(v___x_10512_, 0);
                        lean_inc(v_val_10514_);
                        lean_dec_ref_known(v___x_10512_, 1);
                        v___x_10515_ = l_String_Slice_Pos_get_x3f(v___x_10511_, v_val_10514_);
                        lean_dec(v_val_10514_);
                        lean_dec_ref_known(v___x_10511_, 3);
                        if lean_obj_tag(v___x_10515_) == 0 {
                            v___x_10516_ = 65;
                            v___y_10486_ = v___x_10509_;
                            v___y_10487_ = v___x_10505_;
                            v___y_10488_ = v___x_10504_;
                            v___y_10489_ = v___x_10516_;
                            state = 3;
                            continue;
                        } else {
                            v_val_10517_ = lean_ctor_get(v___x_10515_, 0);
                            lean_inc(v_val_10517_);
                            lean_dec_ref_known(v___x_10515_, 1);
                            v___x_10518_ = lean_unbox_uint32(v_val_10517_);
                            lean_dec(v_val_10517_);
                            v___y_10486_ = v___x_10509_;
                            v___y_10487_ = v___x_10505_;
                            v___y_10488_ = v___x_10504_;
                            v___y_10489_ = v___x_10518_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_10502_;
            }
            6 => {
                if v_isShared_10535_ == 0 {
                    v___x_10537_ = v___x_10534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_10538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10538_, 0, v_a_10532_);
                    v___x_10537_ = v_reuseFailAlloc_10538_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_10537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(
    mut v_s_10540_: *mut LeanObject,
    mut v_lines_10541_: *mut LeanObject,
    mut v_a_10542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10543_: *mut LeanObject = core::ptr::null_mut();
    v_res_10543_ =
        l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_10540_, v_lines_10541_);
    return v_res_10543_;
}
pub unsafe fn l_IO_FS_Stream_lines(mut v_s_10544_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10547_: *mut LeanObject = core::ptr::null_mut();
    v___x_10546_ = l_IO_FS_Handle_lines___closed__0;
    v___x_10547_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_10544_, v___x_10546_);
    return v___x_10547_;
}
pub unsafe fn l_IO_FS_Stream_lines___boxed(
    mut v_s_10548_: *mut LeanObject,
    mut v_a_10549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10550_: *mut LeanObject = core::ptr::null_mut();
    v_res_10550_ = l_IO_FS_Stream_lines(v_s_10548_);
    return v_res_10550_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__0(
    mut v_bOut_10551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10553_: *mut LeanObject = core::ptr::null_mut();
    v___x_10553_ = lean_st_ref_get(v_bOut_10551_);
    return v___x_10553_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(
    mut v_bOut_10554_: *mut LeanObject,
    mut v___y_10555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10556_: *mut LeanObject = core::ptr::null_mut();
    v_res_10556_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_10554_);
    lean_dec(v_bOut_10554_);
    return v_res_10556_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_10561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10566_: *mut LeanObject = core::ptr::null_mut();
    v___x_10561_ = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3;
    v___x_10562_ = lean_unsigned_to_nat(46);
    v___x_10563_ = lean_unsigned_to_nat(193);
    v___x_10564_ = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2;
    v___x_10565_ = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1;
    v___x_10566_ = l_mkPanicMessageWithDecl(
        v___x_10565_,
        v___x_10564_,
        v___x_10563_,
        v___x_10562_,
        v___x_10561_,
    );
    return v___x_10566_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__1(
    mut v_r_10567_: *mut LeanObject,
    mut v_toPure_10568_: *mut LeanObject,
    mut v_bOut_10569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_10574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10575_: u8 = 0;
    let mut v___x_10576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_10574_ = lean_ctor_get(v_bOut_10569_, 0);
                lean_inc_ref(v_data_10574_);
                lean_dec_ref(v_bOut_10569_);
                v___x_10575_ = lean_string_validate_utf8(v_data_10574_);
                if v___x_10575_ == 0 {
                    lean_dec_ref(v_data_10574_);
                    v___x_10576_ = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
                    v___x_10577_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once
                        ),
                        _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4,
                    );
                    v___x_10578_ = l_panic___redArg(v___x_10576_, v___x_10577_);
                    v___y_10571_ = v___x_10578_;
                    state = 1;
                    continue;
                } else {
                    v___x_10579_ = lean_string_from_utf8_unchecked(v_data_10574_);
                    v___y_10571_ = v___x_10579_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10572_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_10572_, 0, v___y_10571_);
                lean_ctor_set(v___x_10572_, 1, v_r_10567_);
                v___x_10573_ = lean_apply_2(v_toPure_10568_, lean_box(0), v___x_10572_);
                return v___x_10573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__2(
    mut v_toPure_10580_: *mut LeanObject,
    mut v_inst_10581_: *mut LeanObject,
    mut v___f_10582_: *mut LeanObject,
    mut v_toBind_10583_: *mut LeanObject,
    mut v_r_10584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10587_: *mut LeanObject = core::ptr::null_mut();
    v___f_10585_ = lean_alloc_closure(
        l_IO_FS_withIsolatedStreams___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_10585_, 0, v_r_10584_);
    lean_closure_set(v___f_10585_, 1, v_toPure_10580_);
    v___x_10586_ = lean_apply_2(v_inst_10581_, lean_box(0), v___f_10582_);
    v___x_10587_ = lean_apply_4(
        v_toBind_10583_,
        lean_box(0),
        lean_box(0),
        v___x_10586_,
        v___f_10585_,
    );
    return v___x_10587_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__3(
    mut v_toPure_10588_: *mut LeanObject,
    mut v_inst_10589_: *mut LeanObject,
    mut v_toBind_10590_: *mut LeanObject,
    mut v_bIn_10591_: *mut LeanObject,
    mut v_inst_10592_: *mut LeanObject,
    mut v_inst_10593_: *mut LeanObject,
    mut v_isolateStderr_10594_: u8,
    mut v_x_10595_: *mut LeanObject,
    mut v_bOut_10596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10606_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_bOut_10596_);
                v___f_10597_ = lean_alloc_closure(
                    l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_10597_, 0, v_bOut_10596_);
                lean_inc(v_toBind_10590_);
                lean_inc(v_inst_10589_);
                v___f_10598_ = lean_alloc_closure(
                    l_IO_FS_withIsolatedStreams___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_10598_, 0, v_toPure_10588_);
                lean_closure_set(v___f_10598_, 1, v_inst_10589_);
                lean_closure_set(v___f_10598_, 2, v___f_10597_);
                lean_closure_set(v___f_10598_, 3, v_toBind_10590_);
                v___x_10599_ = l_IO_FS_Stream_ofBuffer(v_bIn_10591_);
                v___x_10600_ = l_IO_FS_Stream_ofBuffer(v_bOut_10596_);
                if v_isolateStderr_10594_ == 0 {
                    v___y_10602_ = v_x_10595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v___x_10600_);
                    lean_inc(v_inst_10589_);
                    lean_inc(v_inst_10593_);
                    lean_inc_ref(v_inst_10592_);
                    v___x_10606_ = l_IO_withStderr___redArg(
                        v_inst_10592_,
                        v_inst_10593_,
                        v_inst_10589_,
                        v___x_10600_,
                        v_x_10595_,
                    );
                    v___y_10602_ = v___x_10606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_10589_);
                lean_inc(v_inst_10593_);
                lean_inc_ref(v_inst_10592_);
                v___x_10603_ = l_IO_withStdout___redArg(
                    v_inst_10592_,
                    v_inst_10593_,
                    v_inst_10589_,
                    v___x_10600_,
                    v___y_10602_,
                );
                v___x_10604_ = l_IO_withStdin___redArg(
                    v_inst_10592_,
                    v_inst_10593_,
                    v_inst_10589_,
                    v___x_10599_,
                    v___x_10603_,
                );
                v___x_10605_ = lean_apply_4(
                    v_toBind_10590_,
                    lean_box(0),
                    lean_box(0),
                    v___x_10604_,
                    v___f_10598_,
                );
                return v___x_10605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(
    mut v_toPure_10607_: *mut LeanObject,
    mut v_inst_10608_: *mut LeanObject,
    mut v_toBind_10609_: *mut LeanObject,
    mut v_bIn_10610_: *mut LeanObject,
    mut v_inst_10611_: *mut LeanObject,
    mut v_inst_10612_: *mut LeanObject,
    mut v_isolateStderr_10613_: *mut LeanObject,
    mut v_x_10614_: *mut LeanObject,
    mut v_bOut_10615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isolateStderr_boxed_10616_: u8 = 0;
    let mut v_res_10617_: *mut LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_10616_ = (lean_unbox(v_isolateStderr_10613_) as u8);
    v_res_10617_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(
        v_toPure_10607_,
        v_inst_10608_,
        v_toBind_10609_,
        v_bIn_10610_,
        v_inst_10611_,
        v_inst_10612_,
        v_isolateStderr_boxed_10616_,
        v_x_10614_,
        v_bOut_10615_,
    );
    return v_res_10617_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__4(
    mut v_toPure_10618_: *mut LeanObject,
    mut v_inst_10619_: *mut LeanObject,
    mut v_toBind_10620_: *mut LeanObject,
    mut v_inst_10621_: *mut LeanObject,
    mut v_inst_10622_: *mut LeanObject,
    mut v_isolateStderr_10623_: u8,
    mut v_x_10624_: *mut LeanObject,
    mut v___x_10625_: *mut LeanObject,
    mut v_bIn_10626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10629_: *mut LeanObject = core::ptr::null_mut();
    v___x_10627_ = lean_box((v_isolateStderr_10623_) as usize);
    lean_inc(v_toBind_10620_);
    v___f_10628_ = lean_alloc_closure(
        l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_10628_, 0, v_toPure_10618_);
    lean_closure_set(v___f_10628_, 1, v_inst_10619_);
    lean_closure_set(v___f_10628_, 2, v_toBind_10620_);
    lean_closure_set(v___f_10628_, 3, v_bIn_10626_);
    lean_closure_set(v___f_10628_, 4, v_inst_10621_);
    lean_closure_set(v___f_10628_, 5, v_inst_10622_);
    lean_closure_set(v___f_10628_, 6, v___x_10627_);
    lean_closure_set(v___f_10628_, 7, v_x_10624_);
    v___x_10629_ = lean_apply_4(
        v_toBind_10620_,
        lean_box(0),
        lean_box(0),
        v___x_10625_,
        v___f_10628_,
    );
    return v___x_10629_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(
    mut v_toPure_10630_: *mut LeanObject,
    mut v_inst_10631_: *mut LeanObject,
    mut v_toBind_10632_: *mut LeanObject,
    mut v_inst_10633_: *mut LeanObject,
    mut v_inst_10634_: *mut LeanObject,
    mut v_isolateStderr_10635_: *mut LeanObject,
    mut v_x_10636_: *mut LeanObject,
    mut v___x_10637_: *mut LeanObject,
    mut v_bIn_10638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isolateStderr_boxed_10639_: u8 = 0;
    let mut v_res_10640_: *mut LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_10639_ = (lean_unbox(v_isolateStderr_10635_) as u8);
    v_res_10640_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(
        v_toPure_10630_,
        v_inst_10631_,
        v_toBind_10632_,
        v_inst_10633_,
        v_inst_10634_,
        v_isolateStderr_boxed_10639_,
        v_x_10636_,
        v___x_10637_,
        v_bIn_10638_,
    );
    return v_res_10640_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_10641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10643_: *mut LeanObject = core::ptr::null_mut();
    v___x_10641_ = lean_unsigned_to_nat(0);
    v___x_10642_ = l_ByteArray_empty;
    v___x_10643_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10643_, 0, v___x_10642_);
    lean_ctor_set(v___x_10643_, 1, v___x_10641_);
    return v___x_10643_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_10644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10645_: *mut LeanObject = core::ptr::null_mut();
    v___x_10644_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___redArg___closed__0),
        core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___redArg___closed__0_once),
        _init_l_IO_FS_withIsolatedStreams___redArg___closed__0,
    );
    v___x_10645_ = lean_alloc_closure(l_IO_mkRef___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_10645_, 0, lean_box(0));
    lean_closure_set(v___x_10645_, 1, v___x_10644_);
    return v___x_10645_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg(
    mut v_inst_10646_: *mut LeanObject,
    mut v_inst_10647_: *mut LeanObject,
    mut v_inst_10648_: *mut LeanObject,
    mut v_x_10649_: *mut LeanObject,
    mut v_isolateStderr_10650_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_10651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10658_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10651_ = lean_ctor_get(v_inst_10646_, 0);
    v_toBind_10652_ = lean_ctor_get(v_inst_10646_, 1);
    lean_inc_n(v_toBind_10652_, 2);
    v_toPure_10653_ = lean_ctor_get(v_toApplicative_10651_, 1);
    lean_inc(v_toPure_10653_);
    v___x_10654_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___redArg___closed__1),
        core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___redArg___closed__1_once),
        _init_l_IO_FS_withIsolatedStreams___redArg___closed__1,
    );
    lean_inc(v_inst_10648_);
    v___x_10655_ = lean_apply_2(v_inst_10648_, lean_box(0), v___x_10654_);
    v___x_10656_ = lean_box((v_isolateStderr_10650_) as usize);
    lean_inc(v___x_10655_);
    v___f_10657_ = lean_alloc_closure(
        l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_10657_, 0, v_toPure_10653_);
    lean_closure_set(v___f_10657_, 1, v_inst_10648_);
    lean_closure_set(v___f_10657_, 2, v_toBind_10652_);
    lean_closure_set(v___f_10657_, 3, v_inst_10646_);
    lean_closure_set(v___f_10657_, 4, v_inst_10647_);
    lean_closure_set(v___f_10657_, 5, v___x_10656_);
    lean_closure_set(v___f_10657_, 6, v_x_10649_);
    lean_closure_set(v___f_10657_, 7, v___x_10655_);
    v___x_10658_ = lean_apply_4(
        v_toBind_10652_,
        lean_box(0),
        lean_box(0),
        v___x_10655_,
        v___f_10657_,
    );
    return v___x_10658_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___redArg___boxed(
    mut v_inst_10659_: *mut LeanObject,
    mut v_inst_10660_: *mut LeanObject,
    mut v_inst_10661_: *mut LeanObject,
    mut v_x_10662_: *mut LeanObject,
    mut v_isolateStderr_10663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isolateStderr_boxed_10664_: u8 = 0;
    let mut v_res_10665_: *mut LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_10664_ = (lean_unbox(v_isolateStderr_10663_) as u8);
    v_res_10665_ = l_IO_FS_withIsolatedStreams___redArg(
        v_inst_10659_,
        v_inst_10660_,
        v_inst_10661_,
        v_x_10662_,
        v_isolateStderr_boxed_10664_,
    );
    return v_res_10665_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams(
    mut v_m_10666_: *mut LeanObject,
    mut v_00_u03b1_10667_: *mut LeanObject,
    mut v_inst_10668_: *mut LeanObject,
    mut v_inst_10669_: *mut LeanObject,
    mut v_inst_10670_: *mut LeanObject,
    mut v_x_10671_: *mut LeanObject,
    mut v_isolateStderr_10672_: u8,
) -> *mut LeanObject {
    let mut v___x_10673_: *mut LeanObject = core::ptr::null_mut();
    v___x_10673_ = l_IO_FS_withIsolatedStreams___redArg(
        v_inst_10668_,
        v_inst_10669_,
        v_inst_10670_,
        v_x_10671_,
        v_isolateStderr_10672_,
    );
    return v___x_10673_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___boxed(
    mut v_m_10674_: *mut LeanObject,
    mut v_00_u03b1_10675_: *mut LeanObject,
    mut v_inst_10676_: *mut LeanObject,
    mut v_inst_10677_: *mut LeanObject,
    mut v_inst_10678_: *mut LeanObject,
    mut v_x_10679_: *mut LeanObject,
    mut v_isolateStderr_10680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isolateStderr_boxed_10681_: u8 = 0;
    let mut v_res_10682_: *mut LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_10681_ = (lean_unbox(v_isolateStderr_10680_) as u8);
    v_res_10682_ = l_IO_FS_withIsolatedStreams(
        v_m_10674_,
        v_00_u03b1_10675_,
        v_inst_10676_,
        v_inst_10677_,
        v_inst_10678_,
        v_x_10679_,
        v_isolateStderr_boxed_10681_,
    );
    return v_res_10682_;
}
pub unsafe fn _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9()
-> *mut LeanObject {
    let mut v___x_10739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10740_: *mut LeanObject = core::ptr::null_mut();
    v___x_10739_ = l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0;
    v___x_10740_ = l_String_toRawSubstring_x27(v___x_10739_);
    return v___x_10740_;
}
pub unsafe fn _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17()
-> *mut LeanObject {
    let mut v___x_10755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10756_: *mut LeanObject = core::ptr::null_mut();
    v___x_10755_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
    v___x_10756_ = l_String_toRawSubstring_x27(v___x_10755_);
    return v___x_10756_;
}
pub unsafe fn _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24()
-> *mut LeanObject {
    let mut v___x_10769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10770_: *mut LeanObject = core::ptr::null_mut();
    v___x_10769_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
    v___x_10770_ = l_String_toRawSubstring_x27(v___x_10769_);
    return v___x_10770_;
}
pub unsafe fn _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31()
-> *mut LeanObject {
    let mut v___x_10785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10786_: *mut LeanObject = core::ptr::null_mut();
    v___x_10785_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
    v___x_10786_ = l_String_toRawSubstring_x27(v___x_10785_);
    return v___x_10786_;
}
pub unsafe fn l___aux__Init__System__IO______macroRules__termPrintln_x21______1(
    mut v_x_10811_: *mut LeanObject,
    mut v_a_10812_: *mut LeanObject,
    mut v_a_10813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10815_: u8 = 0;
    v___x_10814_ = l_termPrintln_x21_____00__closed__1;
    lean_inc(v_x_10811_);
    v___x_10815_ = l_Lean_Syntax_isOfKind(v_x_10811_, v___x_10814_);
    if v___x_10815_ == 0 {
        let mut v___x_10816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10817_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_10811_);
        v___x_10816_ = lean_box(1);
        v___x_10817_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_10817_, 0, v___x_10816_);
        lean_ctor_set(v___x_10817_, 1, v_a_10813_);
        return v___x_10817_;
    } else {
        let mut v___x_10818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10821_: u8 = 0;
        v___x_10818_ = lean_unsigned_to_nat(1);
        v___x_10819_ = l_Lean_Syntax_getArg(v_x_10811_, v___x_10818_);
        lean_dec(v_x_10811_);
        v___x_10820_ =
            l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
        lean_inc(v___x_10819_);
        v___x_10821_ = l_Lean_Syntax_isOfKind(v___x_10819_, v___x_10820_);
        if v___x_10821_ == 0 {
            let mut v_quotContext_10822_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_10823_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_10824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10827_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10828_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10829_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10830_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10831_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10832_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10833_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10834_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10835_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10836_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10837_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10839_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10840_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10841_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10842_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10843_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10847_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10848_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10849_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10850_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10851_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10852_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10853_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10854_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10855_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10857_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10860_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10865_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_10822_ = lean_ctor_get(v_a_10812_, 1);
            v_currMacroScope_10823_ = lean_ctor_get(v_a_10812_, 2);
            v_ref_10824_ = lean_ctor_get(v_a_10812_, 5);
            v___x_10825_ = l_Lean_SourceInfo_fromRef(v_ref_10824_, v___x_10821_);
            v___x_10826_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
            v___x_10827_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
            v___x_10828_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
            lean_inc_n(v___x_10825_, 14);
            v___x_10829_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10829_, 0, v___x_10825_);
            lean_ctor_set(v___x_10829_, 1, v___x_10828_);
            v___x_10830_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
            v___x_10831_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
            v___x_10832_ = lean_box(0);
            lean_inc_n(v_currMacroScope_10823_, 4);
            lean_inc_n(v_quotContext_10822_, 4);
            v___x_10833_ =
                l_Lean_addMacroScope(v_quotContext_10822_, v___x_10832_, v_currMacroScope_10823_);
            v___x_10834_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
            v___x_10835_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10835_, 0, v___x_10825_);
            lean_ctor_set(v___x_10835_, 1, v___x_10831_);
            lean_ctor_set(v___x_10835_, 2, v___x_10833_);
            lean_ctor_set(v___x_10835_, 3, v___x_10834_);
            v___x_10836_ = l_Lean_Syntax_node1(v___x_10825_, v___x_10830_, v___x_10835_);
            v___x_10837_ =
                l_Lean_Syntax_node2(v___x_10825_, v___x_10827_, v___x_10829_, v___x_10836_);
            v___x_10838_ = l_IO_waitAny___auto__1___closed__16;
            v___x_10839_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
            v___x_10840_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
            v___x_10841_ =
                l_Lean_addMacroScope(v_quotContext_10822_, v___x_10840_, v_currMacroScope_10823_);
            v___x_10842_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
            v___x_10843_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10843_, 0, v___x_10825_);
            lean_ctor_set(v___x_10843_, 1, v___x_10839_);
            lean_ctor_set(v___x_10843_, 2, v___x_10841_);
            lean_ctor_set(v___x_10843_, 3, v___x_10842_);
            v___x_10844_ = l_IO_waitAny___auto__1___closed__9;
            v___x_10845_ = l_Lean_Syntax_node1(v___x_10825_, v___x_10844_, v___x_10819_);
            v___x_10846_ =
                l_Lean_Syntax_node2(v___x_10825_, v___x_10838_, v___x_10843_, v___x_10845_);
            v___x_10847_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
            v___x_10848_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10848_, 0, v___x_10825_);
            lean_ctor_set(v___x_10848_, 1, v___x_10847_);
            v___x_10849_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
            v___x_10850_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
            v___x_10851_ =
                l_Lean_addMacroScope(v_quotContext_10822_, v___x_10850_, v_currMacroScope_10823_);
            v___x_10852_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
            v___x_10853_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10853_, 0, v___x_10825_);
            lean_ctor_set(v___x_10853_, 1, v___x_10849_);
            lean_ctor_set(v___x_10853_, 2, v___x_10851_);
            lean_ctor_set(v___x_10853_, 3, v___x_10852_);
            v___x_10854_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
            v___x_10855_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
            v___x_10856_ =
                l_Lean_addMacroScope(v_quotContext_10822_, v___x_10855_, v_currMacroScope_10823_);
            v___x_10857_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
            v___x_10858_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10858_, 0, v___x_10825_);
            lean_ctor_set(v___x_10858_, 1, v___x_10854_);
            lean_ctor_set(v___x_10858_, 2, v___x_10856_);
            lean_ctor_set(v___x_10858_, 3, v___x_10857_);
            v___x_10859_ = l_Lean_Syntax_node1(v___x_10825_, v___x_10844_, v___x_10858_);
            v___x_10860_ =
                l_Lean_Syntax_node2(v___x_10825_, v___x_10838_, v___x_10853_, v___x_10859_);
            v___x_10861_ = l_Lean_Syntax_node1(v___x_10825_, v___x_10844_, v___x_10860_);
            v___x_10862_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
            v___x_10863_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10863_, 0, v___x_10825_);
            lean_ctor_set(v___x_10863_, 1, v___x_10862_);
            v___x_10864_ = l_Lean_Syntax_node5(
                v___x_10825_,
                v___x_10826_,
                v___x_10837_,
                v___x_10846_,
                v___x_10848_,
                v___x_10861_,
                v___x_10863_,
            );
            v___x_10865_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_10865_, 0, v___x_10864_);
            lean_ctor_set(v___x_10865_, 1, v_a_10813_);
            return v___x_10865_;
        } else {
            let mut v_quotContext_10866_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_10867_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_10868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10869_: u8 = 0;
            let mut v___x_10870_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10872_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10873_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10874_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10875_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10876_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10877_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10878_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10879_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10880_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10881_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10882_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10883_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10888_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10889_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10891_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10892_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10893_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10894_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10899_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10900_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10901_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10902_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10903_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10904_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10905_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10906_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10907_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10908_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10909_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10910_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10911_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10912_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10913_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10914_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10915_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10916_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_10866_ = lean_ctor_get(v_a_10812_, 1);
            v_currMacroScope_10867_ = lean_ctor_get(v_a_10812_, 2);
            v_ref_10868_ = lean_ctor_get(v_a_10812_, 5);
            v___x_10869_ = 0;
            v___x_10870_ = l_Lean_SourceInfo_fromRef(v_ref_10868_, v___x_10869_);
            v___x_10871_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
            v___x_10872_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
            v___x_10873_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
            lean_inc_n(v___x_10870_, 17);
            v___x_10874_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10874_, 0, v___x_10870_);
            lean_ctor_set(v___x_10874_, 1, v___x_10873_);
            v___x_10875_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
            v___x_10876_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
            v___x_10877_ = lean_box(0);
            lean_inc_n(v_currMacroScope_10867_, 4);
            lean_inc_n(v_quotContext_10866_, 4);
            v___x_10878_ =
                l_Lean_addMacroScope(v_quotContext_10866_, v___x_10877_, v_currMacroScope_10867_);
            v___x_10879_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
            v___x_10880_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10880_, 0, v___x_10870_);
            lean_ctor_set(v___x_10880_, 1, v___x_10876_);
            lean_ctor_set(v___x_10880_, 2, v___x_10878_);
            lean_ctor_set(v___x_10880_, 3, v___x_10879_);
            v___x_10881_ = l_Lean_Syntax_node1(v___x_10870_, v___x_10875_, v___x_10880_);
            v___x_10882_ =
                l_Lean_Syntax_node2(v___x_10870_, v___x_10872_, v___x_10874_, v___x_10881_);
            v___x_10883_ = l_IO_waitAny___auto__1___closed__16;
            v___x_10884_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
            v___x_10885_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
            v___x_10886_ =
                l_Lean_addMacroScope(v_quotContext_10866_, v___x_10885_, v_currMacroScope_10867_);
            v___x_10887_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
            v___x_10888_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10888_, 0, v___x_10870_);
            lean_ctor_set(v___x_10888_, 1, v___x_10884_);
            lean_ctor_set(v___x_10888_, 2, v___x_10886_);
            lean_ctor_set(v___x_10888_, 3, v___x_10887_);
            v___x_10889_ = l_IO_waitAny___auto__1___closed__9;
            v___x_10890_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
            v___x_10891_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
            v___x_10892_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
            v___x_10893_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10893_, 0, v___x_10870_);
            lean_ctor_set(v___x_10893_, 1, v___x_10892_);
            v___x_10894_ =
                l_Lean_Syntax_node2(v___x_10870_, v___x_10891_, v___x_10893_, v___x_10819_);
            v___x_10895_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
            v___x_10896_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10896_, 0, v___x_10870_);
            lean_ctor_set(v___x_10896_, 1, v___x_10895_);
            lean_inc_ref(v___x_10896_);
            lean_inc(v___x_10882_);
            v___x_10897_ = l_Lean_Syntax_node3(
                v___x_10870_,
                v___x_10890_,
                v___x_10882_,
                v___x_10894_,
                v___x_10896_,
            );
            v___x_10898_ = l_Lean_Syntax_node1(v___x_10870_, v___x_10889_, v___x_10897_);
            v___x_10899_ =
                l_Lean_Syntax_node2(v___x_10870_, v___x_10883_, v___x_10888_, v___x_10898_);
            v___x_10900_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
            v___x_10901_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_10901_, 0, v___x_10870_);
            lean_ctor_set(v___x_10901_, 1, v___x_10900_);
            v___x_10902_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
            v___x_10903_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
            v___x_10904_ =
                l_Lean_addMacroScope(v_quotContext_10866_, v___x_10903_, v_currMacroScope_10867_);
            v___x_10905_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
            v___x_10906_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10906_, 0, v___x_10870_);
            lean_ctor_set(v___x_10906_, 1, v___x_10902_);
            lean_ctor_set(v___x_10906_, 2, v___x_10904_);
            lean_ctor_set(v___x_10906_, 3, v___x_10905_);
            v___x_10907_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31), core::ptr::addr_of_mut!(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once), _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
            v___x_10908_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
            v___x_10909_ =
                l_Lean_addMacroScope(v_quotContext_10866_, v___x_10908_, v_currMacroScope_10867_);
            v___x_10910_ =
                l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
            v___x_10911_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_10911_, 0, v___x_10870_);
            lean_ctor_set(v___x_10911_, 1, v___x_10907_);
            lean_ctor_set(v___x_10911_, 2, v___x_10909_);
            lean_ctor_set(v___x_10911_, 3, v___x_10910_);
            v___x_10912_ = l_Lean_Syntax_node1(v___x_10870_, v___x_10889_, v___x_10911_);
            v___x_10913_ =
                l_Lean_Syntax_node2(v___x_10870_, v___x_10883_, v___x_10906_, v___x_10912_);
            v___x_10914_ = l_Lean_Syntax_node1(v___x_10870_, v___x_10889_, v___x_10913_);
            v___x_10915_ = l_Lean_Syntax_node5(
                v___x_10870_,
                v___x_10871_,
                v___x_10882_,
                v___x_10899_,
                v___x_10901_,
                v___x_10914_,
                v___x_10896_,
            );
            v___x_10916_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_10916_, 0, v___x_10915_);
            lean_ctor_set(v___x_10916_, 1, v_a_10813_);
            return v___x_10916_;
        }
    }
}
pub unsafe fn l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(
    mut v_x_10917_: *mut LeanObject,
    mut v_a_10918_: *mut LeanObject,
    mut v_a_10919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10920_: *mut LeanObject = core::ptr::null_mut();
    v_res_10920_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(
        v_x_10917_, v_a_10918_, v_a_10919_,
    );
    lean_dec_ref(v_a_10918_);
    return v_res_10920_;
}
pub unsafe fn l_Runtime_markMultiThreaded___boxed(
    mut v_00_u03b1_10924_: *mut LeanObject,
    mut v_a_10925_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10927_: *mut LeanObject = core::ptr::null_mut();
    v_res_10927_ = lean_runtime_mark_multi_threaded(v_a_10925_);
    return v_res_10927_;
}
pub unsafe fn l_Runtime_markPersistent___boxed(
    mut v_00_u03b1_10931_: *mut LeanObject,
    mut v_a_10932_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10934_: *mut LeanObject = core::ptr::null_mut();
    v_res_10934_ = lean_runtime_mark_persistent(v_a_10932_);
    return v_res_10934_;
}
pub unsafe fn l_Runtime_forget___boxed(
    mut v_00_u03b1_10938_: *mut LeanObject,
    mut v_a_10939_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10941_: *mut LeanObject = core::ptr::null_mut();
    v_res_10941_ = lean_runtime_forget(v_a_10939_);
    return v_res_10941_;
}
pub unsafe fn l_Runtime_hold___boxed(
    mut v_00_u03b1_10945_: *mut LeanObject,
    mut v_a_10946_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_10947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10948_: *mut LeanObject = core::ptr::null_mut();
    v_res_10948_ = lean_runtime_hold(v_a_10946_);
    lean_dec(v_a_10946_);
    return v_res_10948_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_IO(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_IOError(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_IO_RealWorld_nonemptyType = _init_l_IO_RealWorld_nonemptyType();
    l_IO_instInhabitedTaskState_default = _init_l_IO_instInhabitedTaskState_default();
    l_IO_instInhabitedTaskState = _init_l_IO_instInhabitedTaskState();
    l_IO_instLTTaskState = _init_l_IO_instLTTaskState();
    lean_mark_persistent(l_IO_instLTTaskState);
    l_IO_instLETaskState = _init_l_IO_instLETaskState();
    lean_mark_persistent(l_IO_instLETaskState);
    l_IO_FS_instInhabitedSystemTime_default = _init_l_IO_FS_instInhabitedSystemTime_default();
    lean_mark_persistent(l_IO_FS_instInhabitedSystemTime_default);
    l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
    lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
    l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
    lean_mark_persistent(l_IO_FS_instLTSystemTime);
    l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
    lean_mark_persistent(l_IO_FS_instLESystemTime);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_IO(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_IO_waitAny___auto__1 = _init_l_IO_waitAny___auto__1();
    lean_mark_persistent(l_IO_waitAny___auto__1);
    l_IO_waitAny_x27___auto__1 = _init_l_IO_waitAny_x27___auto__1();
    lean_mark_persistent(l_IO_waitAny_x27___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_IO(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_IOError(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_IO(builtin);
}
