// Lean compiler output
// Module: Lean.Elab.Deriving.Nonempty
// Imports: Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_mkCIdent, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, l_Lean_Elab_registerDerivingHandler,
    runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Deriving::Util::{
    initialize_Lean_Elab_Deriving_Util, l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg,
    runtime_initialize_Lean_Elab_Deriving_Util,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::l_Lean_Expr_fvarId_x21;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getUserName___redArg,
};
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_decLevel_x3f;
use crate::r#gen::Lean::MonadEnv::{l_Lean_isInductiveCore, l_Lean_isInductiveCore_x3f};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value) as *mut LeanObject,6962862263136859431 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value) as *mut LeanObject,16363371701764479942 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value) as *mut LeanObject,13229434762204987278 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value) as *mut LeanObject,12695378809397736991 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value) as *mut LeanObject,13290931718435096973 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value) as *mut LeanObject,14997215300048349804 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 46, 111, 102, 78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 102, 78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value) as *mut LeanObject,10854111772627758120 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value) as *mut LeanObject,885287005709150661 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value) as *mut LeanObject,745669085263777601 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value) as *mut LeanObject,11908940511024668154 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value) as *mut LeanObject,11064845058293668901 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value) as *mut LeanObject,5940551064397964566 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value) as *mut LeanObject,15755466758005450470 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value) as *mut LeanObject,13585030837571646948 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value) as *mut LeanObject,980513800819686544 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value) as *mut LeanObject,12551601070224435259 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value) as *mut LeanObject;
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0(
    mut v_k_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v_b_1237_: *mut LeanObject,
    mut v_c_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1242_);
    lean_inc_ref(v___y_1241_);
    lean_inc(v___y_1240_);
    lean_inc_ref(v___y_1239_);
    lean_inc(v___y_1236_);
    lean_inc_ref(v___y_1235_);
    v___x_1244_ = lean_apply_9(
        v_k_1234_,
        v_b_1237_,
        v_c_1238_,
        v___y_1235_,
        v___y_1236_,
        v___y_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        lean_box(0),
    );
    return v___x_1244_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0___boxed(
    mut v_k_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v_b_1248_: *mut LeanObject,
    mut v_c_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1255_: *mut LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0(v_k_1245_, v___y_1246_, v___y_1247_, v_b_1248_, v_c_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
    lean_dec(v___y_1253_);
    lean_dec_ref(v___y_1252_);
    lean_dec(v___y_1251_);
    lean_dec_ref(v___y_1250_);
    lean_dec(v___y_1247_);
    lean_dec_ref(v___y_1246_);
    return v_res_1255_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(
    mut v_type_1256_: *mut LeanObject,
    mut v_k_1257_: *mut LeanObject,
    mut v_cleanupAnnotations_1258_: u8,
    mut v_whnfType_1259_: u8,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1261_);
                lean_inc_ref(v___y_1260_);
                v___f_1267_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_1267_, 0, v_k_1257_);
                lean_closure_set(v___f_1267_, 1, v___y_1260_);
                lean_closure_set(v___f_1267_, 2, v___y_1261_);
                v___x_1268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_1256_,
                    v___f_1267_,
                    v_cleanupAnnotations_1258_,
                    v_whnfType_1259_,
                    v___y_1262_,
                    v___y_1263_,
                    v___y_1264_,
                    v___y_1265_,
                );
                if lean_obj_tag(v___x_1268_) == 0 {
                    return v___x_1268_;
                } else {
                    v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
                    v_isSharedCheck_1276_ = (!lean_is_exclusive(v___x_1268_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1271_ = v___x_1268_;
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1269_);
                        lean_dec(v___x_1268_);
                        v___x_1271_ = lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1272_ == 0 {
                    v___x_1274_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
                    v___x_1274_ = v_reuseFailAlloc_1275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___boxed(
    mut v_type_1277_: *mut LeanObject,
    mut v_k_1278_: *mut LeanObject,
    mut v_cleanupAnnotations_1279_: *mut LeanObject,
    mut v_whnfType_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1288_: u8 = 0;
    let mut v_whnfType_boxed_1289_: u8 = 0;
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1288_ = (lean_unbox(v_cleanupAnnotations_1279_) as u8);
    v_whnfType_boxed_1289_ = (lean_unbox(v_whnfType_1280_) as u8);
    v_res_1290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_1277_, v_k_1278_, v_cleanupAnnotations_boxed_1288_, v_whnfType_boxed_1289_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
    lean_dec(v___y_1286_);
    lean_dec_ref(v___y_1285_);
    lean_dec(v___y_1284_);
    lean_dec_ref(v___y_1283_);
    lean_dec(v___y_1282_);
    lean_dec_ref(v___y_1281_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6(
    mut v_00_u03b1_1291_: *mut LeanObject,
    mut v_type_1292_: *mut LeanObject,
    mut v_k_1293_: *mut LeanObject,
    mut v_cleanupAnnotations_1294_: u8,
    mut v_whnfType_1295_: u8,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1303_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_1292_, v_k_1293_, v_cleanupAnnotations_1294_, v_whnfType_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
    return v___x_1303_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___boxed(
    mut v_00_u03b1_1304_: *mut LeanObject,
    mut v_type_1305_: *mut LeanObject,
    mut v_k_1306_: *mut LeanObject,
    mut v_cleanupAnnotations_1307_: *mut LeanObject,
    mut v_whnfType_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1316_: u8 = 0;
    let mut v_whnfType_boxed_1317_: u8 = 0;
    let mut v_res_1318_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1316_ = (lean_unbox(v_cleanupAnnotations_1307_) as u8);
    v_whnfType_boxed_1317_ = (lean_unbox(v_whnfType_1308_) as u8);
    v_res_1318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6(v_00_u03b1_1304_, v_type_1305_, v_k_1306_, v_cleanupAnnotations_boxed_1316_, v_whnfType_boxed_1317_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    lean_dec(v___y_1312_);
    lean_dec_ref(v___y_1311_);
    lean_dec(v___y_1310_);
    lean_dec_ref(v___y_1309_);
    return v_res_1318_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(
    mut v___x_1341_: *mut LeanObject,
    mut v_sz_1342_: usize,
    mut v_i_1343_: usize,
    mut v_bs_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: usize = 0;
    let mut v___x_1360_: usize = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1345_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
                if v___x_1345_ == 0 {
                    lean_dec(v___x_1341_);
                    return v_bs_1344_;
                } else {
                    v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4;
                    v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6;
                    v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8;
                    v_v_1349_ = lean_array_uget(v_bs_1344_, v_i_1343_);
                    v___x_1350_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1351_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1350_);
                    v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10;
                    v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11;
                    lean_inc_n(v___x_1341_, 5);
                    v___x_1354_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1354_, 0, v___x_1341_);
                    lean_ctor_set(v___x_1354_, 1, v___x_1353_);
                    v___x_1355_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1347_, v_v_1349_);
                    v___x_1356_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1346_, v___x_1355_);
                    v___x_1357_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1348_, v___x_1356_);
                    v___x_1358_ =
                        l_Lean_Syntax_node2(v___x_1341_, v___x_1352_, v___x_1354_, v___x_1357_);
                    v___x_1359_ = 1usize;
                    v___x_1360_ = lean_usize_add(v_i_1343_, v___x_1359_);
                    v___x_1361_ = lean_array_uset(v_bs_x27_1351_, v_i_1343_, v___x_1358_);
                    v_i_1343_ = v___x_1360_;
                    v_bs_1344_ = v___x_1361_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___boxed(
    mut v___x_1363_: *mut LeanObject,
    mut v_sz_1364_: *mut LeanObject,
    mut v_i_1365_: *mut LeanObject,
    mut v_bs_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1367_: usize = 0;
    let mut v_i_boxed_1368_: usize = 0;
    let mut v_res_1369_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1364_);
    lean_dec(v_sz_1364_);
    v_i_boxed_1368_ = lean_unbox_usize(v_i_1365_);
    lean_dec(v_i_1365_);
    v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(v___x_1363_, v_sz_boxed_1367_, v_i_boxed_1368_, v_bs_1366_);
    return v_res_1369_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Array_mkArray0(lean_box(0));
    return v___x_1371_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11;
    v___x_1395_ = l_String_toRawSubstring_x27(v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(
    mut v_as_1410_: *mut LeanObject,
    mut v_sz_1411_: usize,
    mut v_i_1412_: usize,
    mut v_b_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
    mut v___y_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: usize = 0;
    let mut v___x_1422_: usize = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_a_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_a_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_a_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut v_a_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1424_ = lean_usize_dec_lt(v_i_1412_, v_sz_1411_);
                if v___x_1424_ == 0 {
                    v___x_1425_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1425_, 0, v_b_1413_);
                    return v___x_1425_;
                } else {
                    v_a_1426_ = lean_array_uget_borrowed(v_as_1410_, v_i_1412_);
                    v___x_1427_ = l_Lean_Expr_fvarId_x21(v_a_1426_);
                    v___x_1428_ = l_Lean_FVarId_getUserName___redArg(
                        v___x_1427_,
                        v___y_1414_,
                        v___y_1416_,
                        v___y_1417_,
                    );
                    if lean_obj_tag(v___x_1428_) == 0 {
                        v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
                        lean_inc(v_a_1429_);
                        lean_dec_ref_known(v___x_1428_, 1);
                        v___x_1430_ = lean_erase_macro_scopes(v_a_1429_);
                        v___x_1431_ =
                            l_Lean_Core_mkFreshUserName(v___x_1430_, v___y_1416_, v___y_1417_);
                        if lean_obj_tag(v___x_1431_) == 0 {
                            v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
                            lean_inc(v_a_1432_);
                            lean_dec_ref_known(v___x_1431_, 1);
                            v_ref_1433_ = lean_ctor_get(v___y_1416_, 5);
                            v_quotContext_1434_ = lean_ctor_get(v___y_1416_, 10);
                            v_currMacroScope_1435_ = lean_ctor_get(v___y_1416_, 11);
                            v___x_1436_ = lean_mk_syntax_ident(v_a_1432_);
                            v___x_1437_ = 0;
                            v___x_1438_ = l_Lean_SourceInfo_fromRef(v_ref_1433_, v___x_1437_);
                            v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0;
                            lean_inc_n(v___x_1438_, 2);
                            v___x_1440_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_1440_, 0, v___x_1438_);
                            lean_ctor_set(v___x_1440_, 1, v___x_1439_);
                            v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6;
                            lean_inc(v___x_1436_);
                            v___x_1442_ =
                                l_Lean_Syntax_node1(v___x_1438_, v___x_1441_, v___x_1436_);
                            lean_inc(v___y_1417_);
                            lean_inc_ref(v___y_1416_);
                            lean_inc(v___y_1415_);
                            lean_inc_ref(v___y_1414_);
                            lean_inc(v_a_1426_);
                            v___x_1443_ = lean_infer_type(
                                v_a_1426_,
                                v___y_1414_,
                                v___y_1415_,
                                v___y_1416_,
                                v___y_1417_,
                            );
                            if lean_obj_tag(v___x_1443_) == 0 {
                                v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
                                lean_inc(v_a_1444_);
                                lean_dec_ref_known(v___x_1443_, 1);
                                lean_inc(v___y_1417_);
                                lean_inc_ref(v___y_1416_);
                                lean_inc(v___y_1415_);
                                lean_inc_ref(v___y_1414_);
                                v___x_1445_ = lean_whnf(
                                    v_a_1444_,
                                    v___y_1414_,
                                    v___y_1415_,
                                    v___y_1416_,
                                    v___y_1417_,
                                );
                                if lean_obj_tag(v___x_1445_) == 0 {
                                    v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
                                    lean_inc(v_a_1446_);
                                    lean_dec_ref_known(v___x_1445_, 1);
                                    v_fst_1447_ = lean_ctor_get(v_b_1413_, 0);
                                    v_snd_1448_ = lean_ctor_get(v_b_1413_, 1);
                                    v_isSharedCheck_1494_ = (!lean_is_exclusive(v_b_1413_)) as u8;
                                    if v_isSharedCheck_1494_ == 0 {
                                        v___x_1450_ = v_b_1413_;
                                        v_isShared_1451_ = v_isSharedCheck_1494_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_1448_);
                                        lean_inc(v_fst_1447_);
                                        lean_dec(v_b_1413_);
                                        v___x_1450_ = lean_box(0);
                                        v_isShared_1451_ = v_isSharedCheck_1494_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_1442_);
                                    lean_dec_ref_known(v___x_1440_, 2);
                                    lean_dec(v___x_1438_);
                                    lean_dec(v___x_1436_);
                                    lean_dec_ref(v_b_1413_);
                                    v_a_1495_ = lean_ctor_get(v___x_1445_, 0);
                                    v_isSharedCheck_1502_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                                    if v_isSharedCheck_1502_ == 0 {
                                        v___x_1497_ = v___x_1445_;
                                        v_isShared_1498_ = v_isSharedCheck_1502_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1495_);
                                        lean_dec(v___x_1445_);
                                        v___x_1497_ = lean_box(0);
                                        v_isShared_1498_ = v_isSharedCheck_1502_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_1442_);
                                lean_dec_ref_known(v___x_1440_, 2);
                                lean_dec(v___x_1438_);
                                lean_dec(v___x_1436_);
                                lean_dec_ref(v_b_1413_);
                                v_a_1503_ = lean_ctor_get(v___x_1443_, 0);
                                v_isSharedCheck_1510_ = (!lean_is_exclusive(v___x_1443_)) as u8;
                                if v_isSharedCheck_1510_ == 0 {
                                    v___x_1505_ = v___x_1443_;
                                    v_isShared_1506_ = v_isSharedCheck_1510_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_1503_);
                                    lean_dec(v___x_1443_);
                                    v___x_1505_ = lean_box(0);
                                    v_isShared_1506_ = v_isSharedCheck_1510_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_1413_);
                            v_a_1511_ = lean_ctor_get(v___x_1431_, 0);
                            v_isSharedCheck_1518_ = (!lean_is_exclusive(v___x_1431_)) as u8;
                            if v_isSharedCheck_1518_ == 0 {
                                v___x_1513_ = v___x_1431_;
                                v_isShared_1514_ = v_isSharedCheck_1518_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_1511_);
                                lean_dec(v___x_1431_);
                                v___x_1513_ = lean_box(0);
                                v_isShared_1514_ = v_isSharedCheck_1518_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_1413_);
                        v_a_1519_ = lean_ctor_get(v___x_1428_, 0);
                        v_isSharedCheck_1526_ = (!lean_is_exclusive(v___x_1428_)) as u8;
                        if v_isSharedCheck_1526_ == 0 {
                            v___x_1521_ = v___x_1428_;
                            v_isShared_1522_ = v_isSharedCheck_1526_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_1519_);
                            lean_dec(v___x_1428_);
                            v___x_1521_ = lean_box(0);
                            v_isShared_1522_ = v_isSharedCheck_1526_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1421_ = 1usize;
                v___x_1422_ = lean_usize_add(v_i_1412_, v___x_1421_);
                v_i_1412_ = v___x_1422_;
                v_b_1413_ = v_a_1420_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1452_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
                lean_inc_n(v___x_1438_, 3);
                v___x_1453_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1453_, 0, v___x_1438_);
                lean_ctor_set(v___x_1453_, 1, v___x_1441_);
                lean_ctor_set(v___x_1453_, 2, v___x_1452_);
                v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3;
                v___x_1455_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1455_, 0, v___x_1438_);
                lean_ctor_set(v___x_1455_, 1, v___x_1454_);
                v___x_1456_ = lean_array_push(v_fst_1447_, v___x_1436_);
                v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5;
                lean_inc_ref(v___x_1453_);
                lean_inc(v___x_1442_);
                v___x_1458_ = l_Lean_Syntax_node4(
                    v___x_1438_,
                    v___x_1457_,
                    v___x_1440_,
                    v___x_1442_,
                    v___x_1453_,
                    v___x_1455_,
                );
                v___x_1459_ = lean_array_push(v_snd_1448_, v___x_1458_);
                if lean_obj_tag(v_a_1446_) == 3 {
                    v_u_1460_ = lean_ctor_get(v_a_1446_, 0);
                    lean_inc(v_u_1460_);
                    lean_dec_ref_known(v_a_1446_, 1);
                    v___x_1461_ = l_Lean_Meta_decLevel_x3f(
                        v_u_1460_,
                        v___y_1414_,
                        v___y_1415_,
                        v___y_1416_,
                        v___y_1417_,
                    );
                    if lean_obj_tag(v___x_1461_) == 0 {
                        v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
                        lean_inc(v_a_1462_);
                        lean_dec_ref_known(v___x_1461_, 1);
                        if lean_obj_tag(v_a_1462_) == 1 {
                            lean_dec_ref_known(v_a_1462_, 1);
                            v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7;
                            v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8;
                            lean_inc_n(v___x_1438_, 4);
                            v___x_1465_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_1465_, 0, v___x_1438_);
                            lean_ctor_set(v___x_1465_, 1, v___x_1464_);
                            v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10;
                            v___x_1467_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
                            v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13;
                            lean_inc(v_currMacroScope_1435_);
                            lean_inc(v_quotContext_1434_);
                            v___x_1469_ = l_Lean_addMacroScope(
                                v_quotContext_1434_,
                                v___x_1468_,
                                v_currMacroScope_1435_,
                            );
                            v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17;
                            v___x_1471_ = lean_alloc_ctor(3, 4, (0) as u32);
                            lean_ctor_set(v___x_1471_, 0, v___x_1438_);
                            lean_ctor_set(v___x_1471_, 1, v___x_1467_);
                            lean_ctor_set(v___x_1471_, 2, v___x_1469_);
                            lean_ctor_set(v___x_1471_, 3, v___x_1470_);
                            v___x_1472_ = l_Lean_Syntax_node2(
                                v___x_1438_,
                                v___x_1466_,
                                v___x_1471_,
                                v___x_1442_,
                            );
                            v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18;
                            v___x_1474_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_1474_, 0, v___x_1438_);
                            lean_ctor_set(v___x_1474_, 1, v___x_1473_);
                            v___x_1475_ = l_Lean_Syntax_node4(
                                v___x_1438_,
                                v___x_1463_,
                                v___x_1465_,
                                v___x_1453_,
                                v___x_1472_,
                                v___x_1474_,
                            );
                            v___x_1476_ = lean_array_push(v___x_1459_, v___x_1475_);
                            if v_isShared_1451_ == 0 {
                                lean_ctor_set(v___x_1450_, 1, v___x_1476_);
                                lean_ctor_set(v___x_1450_, 0, v___x_1456_);
                                v___x_1478_ = v___x_1450_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1456_);
                                lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1476_);
                                v___x_1478_ = v_reuseFailAlloc_1479_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1462_);
                            lean_dec_ref_known(v___x_1453_, 3);
                            lean_dec(v___x_1442_);
                            lean_dec(v___x_1438_);
                            if v_isShared_1451_ == 0 {
                                lean_ctor_set(v___x_1450_, 1, v___x_1459_);
                                lean_ctor_set(v___x_1450_, 0, v___x_1456_);
                                v___x_1481_ = v___x_1450_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1456_);
                                lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1459_);
                                v___x_1481_ = v_reuseFailAlloc_1482_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1459_);
                        lean_dec_ref(v___x_1456_);
                        lean_dec_ref_known(v___x_1453_, 3);
                        lean_del_object(v___x_1450_);
                        lean_dec(v___x_1442_);
                        lean_dec(v___x_1438_);
                        v_a_1483_ = lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1490_ = (!lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1490_ == 0 {
                            v___x_1485_ = v___x_1461_;
                            v_isShared_1486_ = v_isSharedCheck_1490_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1483_);
                            lean_dec(v___x_1461_);
                            v___x_1485_ = lean_box(0);
                            v_isShared_1486_ = v_isSharedCheck_1490_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_1453_, 3);
                    lean_dec(v_a_1446_);
                    lean_dec(v___x_1442_);
                    lean_dec(v___x_1438_);
                    if v_isShared_1451_ == 0 {
                        lean_ctor_set(v___x_1450_, 1, v___x_1459_);
                        lean_ctor_set(v___x_1450_, 0, v___x_1456_);
                        v___x_1492_ = v___x_1450_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1456_);
                        lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1459_);
                        v___x_1492_ = v_reuseFailAlloc_1493_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1420_ = v___x_1478_;
                state = 1;
                continue;
            }
            4 => {
                v_a_1420_ = v___x_1481_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_1486_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1488_;
            }
            7 => {
                v_a_1420_ = v___x_1492_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_1498_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1501_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1500_;
            }
            10 => {
                if v_isShared_1506_ == 0 {
                    v___x_1508_ = v___x_1505_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
                    v___x_1508_ = v_reuseFailAlloc_1509_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1508_;
            }
            12 => {
                if v_isShared_1514_ == 0 {
                    v___x_1516_ = v___x_1513_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1516_;
            }
            14 => {
                if v_isShared_1522_ == 0 {
                    v___x_1524_ = v___x_1521_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
                    v___x_1524_ = v_reuseFailAlloc_1525_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___boxed(
    mut v_as_1527_: *mut LeanObject,
    mut v_sz_1528_: *mut LeanObject,
    mut v_i_1529_: *mut LeanObject,
    mut v_b_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
    mut v___y_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1536_: usize = 0;
    let mut v_i_boxed_1537_: usize = 0;
    let mut v_res_1538_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1528_);
    lean_dec(v_sz_1528_);
    v_i_boxed_1537_ = lean_unbox_usize(v_i_1529_);
    lean_dec(v_i_1529_);
    v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_1527_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
    lean_dec(v___y_1534_);
    lean_dec_ref(v___y_1533_);
    lean_dec(v___y_1532_);
    lean_dec_ref(v___y_1531_);
    lean_dec_ref(v_as_1527_);
    return v_res_1538_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(
    mut v_sz_1539_: usize,
    mut v_i_1540_: usize,
    mut v_bs_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1542_: u8 = 0;
    let mut v_v_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1542_ = lean_usize_dec_lt(v_i_1540_, v_sz_1539_);
                if v___x_1542_ == 0 {
                    return v_bs_1541_;
                } else {
                    v_v_1543_ = lean_array_uget(v_bs_1541_, v_i_1540_);
                    v___x_1544_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1545_ = lean_array_uset(v_bs_1541_, v_i_1540_, v___x_1544_);
                    v___x_1546_ = 1usize;
                    v___x_1547_ = lean_usize_add(v_i_1540_, v___x_1546_);
                    v___x_1548_ = lean_array_uset(v_bs_x27_1545_, v_i_1540_, v_v_1543_);
                    v_i_1540_ = v___x_1547_;
                    v_bs_1541_ = v___x_1548_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4___boxed(
    mut v_sz_1550_: *mut LeanObject,
    mut v_i_1551_: *mut LeanObject,
    mut v_bs_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1553_: usize = 0;
    let mut v_i_boxed_1554_: usize = 0;
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1553_ = lean_unbox_usize(v_sz_1550_);
    lean_dec(v_sz_1550_);
    v_i_boxed_1554_ = lean_unbox_usize(v_i_1551_);
    lean_dec(v_i_1551_);
    v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_boxed_1553_, v_i_boxed_1554_, v_bs_1552_);
    return v_res_1555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(
    mut v_sz_1556_: usize,
    mut v_i_1557_: usize,
    mut v_bs_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1559_: u8 = 0;
    let mut v_v_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1559_ = lean_usize_dec_lt(v_i_1557_, v_sz_1556_);
                if v___x_1559_ == 0 {
                    return v_bs_1558_;
                } else {
                    v_v_1560_ = lean_array_uget(v_bs_1558_, v_i_1557_);
                    v___x_1561_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1562_ = lean_array_uset(v_bs_1558_, v_i_1557_, v___x_1561_);
                    v___x_1563_ = 1usize;
                    v___x_1564_ = lean_usize_add(v_i_1557_, v___x_1563_);
                    v___x_1565_ = lean_array_uset(v_bs_x27_1562_, v_i_1557_, v_v_1560_);
                    v_i_1557_ = v___x_1564_;
                    v_bs_1558_ = v___x_1565_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3___boxed(
    mut v_sz_1567_: *mut LeanObject,
    mut v_i_1568_: *mut LeanObject,
    mut v_bs_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1570_: usize = 0;
    let mut v_i_boxed_1571_: usize = 0;
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1567_);
    lean_dec(v_sz_1567_);
    v_i_boxed_1571_ = lean_unbox_usize(v_i_1568_);
    lean_dec(v_i_1568_);
    v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_boxed_1570_, v_i_boxed_1571_, v_bs_1569_);
    return v_res_1572_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10;
    v___x_1601_ = l_String_toRawSubstring_x27(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(
    mut v_sz_1613_: usize,
    mut v_i_1614_: usize,
    mut v_bs_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1618_ = lean_usize_dec_lt(v_i_1614_, v_sz_1613_);
                if v___x_1618_ == 0 {
                    v___x_1619_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1619_, 0, v_bs_1615_);
                    return v___x_1619_;
                } else {
                    v_ref_1620_ = lean_ctor_get(v___y_1616_, 5);
                    v_quotContext_1621_ = lean_ctor_get(v___y_1616_, 10);
                    v_currMacroScope_1622_ = lean_ctor_get(v___y_1616_, 11);
                    v_v_1623_ = lean_array_uget(v_bs_1615_, v_i_1614_);
                    v___x_1624_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1625_ = lean_array_uset(v_bs_1615_, v_i_1614_, v___x_1624_);
                    v___x_1626_ = 0;
                    v___x_1627_ = l_Lean_SourceInfo_fromRef(v_ref_1620_, v___x_1626_);
                    v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1;
                    v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2;
                    v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3;
                    lean_inc_n(v___x_1627_, 8);
                    v___x_1631_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1631_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1631_, 1, v___x_1629_);
                    v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5;
                    v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6;
                    v___x_1634_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1634_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = l_Lean_mkCIdent(v_v_1623_);
                    v___x_1636_ =
                        l_Lean_Syntax_node2(v___x_1627_, v___x_1632_, v___x_1634_, v___x_1635_);
                    v___x_1637_ =
                        l_Lean_Syntax_node2(v___x_1627_, v___x_1630_, v___x_1631_, v___x_1636_);
                    v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7;
                    v___x_1639_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1639_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1639_, 1, v___x_1638_);
                    v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8;
                    v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9;
                    v___x_1642_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1642_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1642_, 1, v___x_1640_);
                    v___x_1643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11);
                    v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14;
                    lean_inc(v_currMacroScope_1622_);
                    lean_inc(v_quotContext_1621_);
                    v___x_1645_ = l_Lean_addMacroScope(
                        v_quotContext_1621_,
                        v___x_1644_,
                        v_currMacroScope_1622_,
                    );
                    v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16;
                    v___x_1647_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_1647_, 0, v___x_1627_);
                    lean_ctor_set(v___x_1647_, 1, v___x_1643_);
                    lean_ctor_set(v___x_1647_, 2, v___x_1645_);
                    lean_ctor_set(v___x_1647_, 3, v___x_1646_);
                    v___x_1648_ =
                        l_Lean_Syntax_node2(v___x_1627_, v___x_1641_, v___x_1642_, v___x_1647_);
                    v___x_1649_ = l_Lean_Syntax_node3(
                        v___x_1627_,
                        v___x_1628_,
                        v___x_1637_,
                        v___x_1639_,
                        v___x_1648_,
                    );
                    v___x_1650_ = 1usize;
                    v___x_1651_ = lean_usize_add(v_i_1614_, v___x_1650_);
                    v___x_1652_ = lean_array_uset(v_bs_x27_1625_, v_i_1614_, v___x_1649_);
                    v_i_1614_ = v___x_1651_;
                    v_bs_1615_ = v___x_1652_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___boxed(
    mut v_sz_1654_: *mut LeanObject,
    mut v_i_1655_: *mut LeanObject,
    mut v_bs_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1659_: usize = 0;
    let mut v_i_boxed_1660_: usize = 0;
    let mut v_res_1661_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1659_ = lean_unbox_usize(v_sz_1654_);
    lean_dec(v_sz_1654_);
    v_i_boxed_1660_ = lean_unbox_usize(v_i_1655_);
    lean_dec(v_i_1655_);
    v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_boxed_1659_, v_i_boxed_1660_, v_bs_1656_, v___y_1657_);
    lean_dec_ref(v___y_1657_);
    return v_res_1661_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28()
-> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1733_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27;
    v___x_1734_ = l_String_toRawSubstring_x27(v___x_1733_);
    return v___x_1734_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(
    mut v_ctors_1825_: *mut LeanObject,
    mut v_declName_1826_: *mut LeanObject,
    mut v_paramsIndices_1827_: *mut LeanObject,
    mut v_x_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
    mut v___y_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1837_: usize = 0;
    let mut v___x_1838_: usize = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1842_: usize = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v_fst_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v_ref_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1866_: usize = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1908_: usize = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1937_: usize = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_a_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1961_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1836_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1;
                v_sz_1837_ = lean_array_size(v_paramsIndices_1827_);
                v___x_1838_ = 0usize;
                v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_paramsIndices_1827_, v_sz_1837_, v___x_1838_, v___x_1836_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
                if lean_obj_tag(v___x_1839_) == 0 {
                    v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
                    lean_inc(v_a_1840_);
                    lean_dec_ref_known(v___x_1839_, 1);
                    v___x_1841_ = lean_array_mk(v_ctors_1825_);
                    v_sz_1842_ = lean_array_size(v___x_1841_);
                    v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_1842_, v___x_1838_, v___x_1841_, v___y_1833_);
                    if lean_obj_tag(v___x_1843_) == 0 {
                        v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
                        v_isSharedCheck_1957_ = (!lean_is_exclusive(v___x_1843_)) as u8;
                        if v_isSharedCheck_1957_ == 0 {
                            v___x_1846_ = v___x_1843_;
                            v_isShared_1847_ = v_isSharedCheck_1957_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1844_);
                            lean_dec(v___x_1843_);
                            v___x_1846_ = lean_box(0);
                            v_isShared_1847_ = v_isSharedCheck_1957_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1840_);
                        lean_dec(v_declName_1826_);
                        v_a_1958_ = lean_ctor_get(v___x_1843_, 0);
                        v_isSharedCheck_1965_ = (!lean_is_exclusive(v___x_1843_)) as u8;
                        if v_isSharedCheck_1965_ == 0 {
                            v___x_1960_ = v___x_1843_;
                            v_isShared_1961_ = v_isSharedCheck_1965_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1958_);
                            lean_dec(v___x_1843_);
                            v___x_1960_ = lean_box(0);
                            v_isShared_1961_ = v_isSharedCheck_1965_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_1826_);
                    lean_dec(v_ctors_1825_);
                    v_a_1966_ = lean_ctor_get(v___x_1839_, 0);
                    v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1839_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1839_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1966_);
                        lean_dec(v___x_1839_);
                        v___x_1968_ = lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1848_ = lean_ctor_get(v_a_1840_, 0);
                v_snd_1849_ = lean_ctor_get(v_a_1840_, 1);
                v_isSharedCheck_1956_ = (!lean_is_exclusive(v_a_1840_)) as u8;
                if v_isSharedCheck_1956_ == 0 {
                    v___x_1851_ = v_a_1840_;
                    v_isShared_1852_ = v_isSharedCheck_1956_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1849_);
                    lean_inc(v_fst_1848_);
                    lean_dec(v_a_1840_);
                    v___x_1851_ = lean_box(0);
                    v_isShared_1852_ = v_isSharedCheck_1956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ref_1853_ = lean_ctor_get(v___y_1833_, 5);
                v_quotContext_1854_ = lean_ctor_get(v___y_1833_, 10);
                v_currMacroScope_1855_ = lean_ctor_get(v___y_1833_, 11);
                v___x_1856_ = 0;
                v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1856_);
                v___x_1858_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3;
                v___x_1859_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4;
                v___x_1860_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5;
                v___x_1861_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6;
                lean_inc(v___x_1857_);
                if v_isShared_1852_ == 0 {
                    lean_ctor_set_tag(v___x_1851_, 2);
                    lean_ctor_set(v___x_1851_, 1, v___x_1860_);
                    lean_ctor_set(v___x_1851_, 0, v___x_1857_);
                    v___x_1863_ = v___x_1851_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1857_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1860_);
                    v___x_1863_ = v_reuseFailAlloc_1955_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6;
                v___x_1865_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
                v_sz_1866_ = lean_array_size(v_snd_1849_);
                v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_1866_, v___x_1838_, v_snd_1849_);
                v___x_1868_ = l_Array_append___redArg(v___x_1865_, v___x_1867_);
                lean_dec_ref(v___x_1867_);
                lean_inc_n(v___x_1857_, 40);
                v___x_1869_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___x_1857_);
                lean_ctor_set(v___x_1869_, 1, v___x_1864_);
                lean_ctor_set(v___x_1869_, 2, v___x_1868_);
                v___x_1870_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1861_, v___x_1863_, v___x_1869_);
                v___x_1871_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1871_, 0, v___x_1857_);
                lean_ctor_set(v___x_1871_, 1, v___x_1858_);
                v___x_1872_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8;
                v___x_1873_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10;
                v___x_1874_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1874_, 0, v___x_1857_);
                lean_ctor_set(v___x_1874_, 1, v___x_1864_);
                lean_ctor_set(v___x_1874_, 2, v___x_1865_);
                lean_inc_ref_n(v___x_1874_, 13);
                v___x_1875_ = l_Lean_Syntax_node7(
                    v___x_1857_,
                    v___x_1873_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1874_,
                );
                v___x_1876_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11;
                v___x_1877_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12;
                v___x_1878_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14;
                v___x_1879_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1878_, v___x_1874_);
                v___x_1880_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1880_, 0, v___x_1857_);
                lean_ctor_set(v___x_1880_, 1, v___x_1876_);
                v___x_1881_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16;
                v___x_1882_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18;
                v___x_1883_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19;
                v___x_1884_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1884_, 0, v___x_1857_);
                lean_ctor_set(v___x_1884_, 1, v___x_1883_);
                v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10;
                v___x_1886_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
                v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13;
                lean_inc_n(v_currMacroScope_1855_, 2);
                lean_inc_n(v_quotContext_1854_, 2);
                v___x_1888_ =
                    l_Lean_addMacroScope(v_quotContext_1854_, v___x_1887_, v_currMacroScope_1855_);
                v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17;
                v___x_1890_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1890_, 0, v___x_1857_);
                lean_ctor_set(v___x_1890_, 1, v___x_1886_);
                lean_ctor_set(v___x_1890_, 2, v___x_1888_);
                lean_ctor_set(v___x_1890_, 3, v___x_1889_);
                v___x_1891_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21;
                v___x_1892_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23;
                v___x_1893_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24;
                v___x_1894_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1894_, 0, v___x_1857_);
                lean_ctor_set(v___x_1894_, 1, v___x_1893_);
                v___x_1895_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26;
                v___x_1896_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28_once), _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28);
                v___x_1897_ = lean_box(0);
                v___x_1898_ =
                    l_Lean_addMacroScope(v_quotContext_1854_, v___x_1897_, v_currMacroScope_1855_);
                v___x_1899_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49;
                v___x_1900_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1900_, 0, v___x_1857_);
                lean_ctor_set(v___x_1900_, 1, v___x_1896_);
                lean_ctor_set(v___x_1900_, 2, v___x_1898_);
                lean_ctor_set(v___x_1900_, 3, v___x_1899_);
                v___x_1901_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1895_, v___x_1900_);
                v___x_1902_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1892_, v___x_1894_, v___x_1901_);
                v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5;
                v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6;
                v___x_1905_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1905_, 0, v___x_1857_);
                lean_ctor_set(v___x_1905_, 1, v___x_1904_);
                v___x_1906_ = l_Lean_mkCIdent(v_declName_1826_);
                v___x_1907_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1903_, v___x_1905_, v___x_1906_);
                v_sz_1908_ = lean_array_size(v_fst_1848_);
                v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_1908_, v___x_1838_, v_fst_1848_);
                v___x_1910_ = l_Array_append___redArg(v___x_1865_, v___x_1909_);
                lean_dec_ref(v___x_1909_);
                v___x_1911_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1911_, 0, v___x_1857_);
                lean_ctor_set(v___x_1911_, 1, v___x_1864_);
                lean_ctor_set(v___x_1911_, 2, v___x_1910_);
                v___x_1912_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1885_, v___x_1907_, v___x_1911_);
                v___x_1913_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50;
                v___x_1914_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1914_, 0, v___x_1857_);
                lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                v___x_1915_ = l_Lean_Syntax_node3(
                    v___x_1857_,
                    v___x_1891_,
                    v___x_1902_,
                    v___x_1912_,
                    v___x_1914_,
                );
                v___x_1916_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1864_, v___x_1915_);
                v___x_1917_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1885_, v___x_1890_, v___x_1916_);
                v___x_1918_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1882_, v___x_1884_, v___x_1917_);
                v___x_1919_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1881_, v___x_1874_, v___x_1918_);
                v___x_1920_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52;
                v___x_1921_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53;
                v___x_1922_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1922_, 0, v___x_1857_);
                lean_ctor_set(v___x_1922_, 1, v___x_1921_);
                v___x_1923_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55;
                v___x_1924_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56;
                v___x_1925_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1925_, 0, v___x_1857_);
                lean_ctor_set(v___x_1925_, 1, v___x_1924_);
                v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8;
                v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4;
                v___x_1928_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57;
                v___x_1929_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58;
                v___x_1930_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1930_, 0, v___x_1857_);
                lean_ctor_set(v___x_1930_, 1, v___x_1928_);
                v___x_1931_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1929_, v___x_1930_);
                v___x_1932_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59;
                v___x_1933_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1933_, 0, v___x_1857_);
                lean_ctor_set(v___x_1933_, 1, v___x_1932_);
                v___x_1934_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60;
                v___x_1935_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61;
                v___x_1936_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1936_, 0, v___x_1857_);
                lean_ctor_set(v___x_1936_, 1, v___x_1934_);
                v_sz_1937_ = lean_array_size(v_a_1844_);
                v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(v___x_1857_, v_sz_1937_, v___x_1838_, v_a_1844_);
                v___x_1939_ = l_Array_append___redArg(v___x_1865_, v___x_1938_);
                lean_dec_ref(v___x_1938_);
                v___x_1940_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1940_, 0, v___x_1857_);
                lean_ctor_set(v___x_1940_, 1, v___x_1864_);
                lean_ctor_set(v___x_1940_, 2, v___x_1939_);
                v___x_1941_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1935_, v___x_1936_, v___x_1940_);
                v___x_1942_ = l_Lean_Syntax_node3(
                    v___x_1857_,
                    v___x_1864_,
                    v___x_1931_,
                    v___x_1933_,
                    v___x_1941_,
                );
                v___x_1943_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1927_, v___x_1942_);
                v___x_1944_ = l_Lean_Syntax_node1(v___x_1857_, v___x_1926_, v___x_1943_);
                v___x_1945_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1923_, v___x_1925_, v___x_1944_);
                v___x_1946_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64;
                v___x_1947_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1946_, v___x_1874_, v___x_1874_);
                v___x_1948_ = l_Lean_Syntax_node4(
                    v___x_1857_,
                    v___x_1920_,
                    v___x_1922_,
                    v___x_1945_,
                    v___x_1947_,
                    v___x_1874_,
                );
                v___x_1949_ = l_Lean_Syntax_node6(
                    v___x_1857_,
                    v___x_1877_,
                    v___x_1879_,
                    v___x_1880_,
                    v___x_1874_,
                    v___x_1874_,
                    v___x_1919_,
                    v___x_1948_,
                );
                v___x_1950_ =
                    l_Lean_Syntax_node2(v___x_1857_, v___x_1872_, v___x_1875_, v___x_1949_);
                v___x_1951_ = l_Lean_Syntax_node3(
                    v___x_1857_,
                    v___x_1859_,
                    v___x_1870_,
                    v___x_1871_,
                    v___x_1950_,
                );
                if v_isShared_1847_ == 0 {
                    lean_ctor_set(v___x_1846_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1953_;
            }
            5 => {
                if v_isShared_1961_ == 0 {
                    v___x_1963_ = v___x_1960_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
                    v___x_1963_ = v_reuseFailAlloc_1964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1963_;
            }
            7 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed(
    mut v_ctors_1974_: *mut LeanObject,
    mut v_declName_1975_: *mut LeanObject,
    mut v_paramsIndices_1976_: *mut LeanObject,
    mut v_x_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1985_: *mut LeanObject = core::ptr::null_mut();
    v_res_1985_ =
        l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(
            v_ctors_1974_,
            v_declName_1975_,
            v_paramsIndices_1976_,
            v_x_1977_,
            v___y_1978_,
            v___y_1979_,
            v___y_1980_,
            v___y_1981_,
            v___y_1982_,
            v___y_1983_,
        );
    lean_dec(v___y_1983_);
    lean_dec_ref(v___y_1982_);
    lean_dec(v___y_1981_);
    lean_dec_ref(v___y_1980_);
    lean_dec(v___y_1979_);
    lean_dec_ref(v___y_1978_);
    lean_dec_ref(v_x_1977_);
    lean_dec_ref(v_paramsIndices_1976_);
    return v_res_1985_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(
    mut v_msgData_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1992_ = lean_st_ref_get(v___y_1990_);
    v_env_1993_ = lean_ctor_get(v___x_1992_, 0);
    lean_inc_ref(v_env_1993_);
    lean_dec(v___x_1992_);
    v___x_1994_ = lean_st_ref_get(v___y_1988_);
    v_mctx_1995_ = lean_ctor_get(v___x_1994_, 0);
    lean_inc_ref(v_mctx_1995_);
    lean_dec(v___x_1994_);
    v_lctx_1996_ = lean_ctor_get(v___y_1987_, 2);
    v_options_1997_ = lean_ctor_get(v___y_1989_, 2);
    lean_inc_ref(v_options_1997_);
    lean_inc_ref(v_lctx_1996_);
    v___x_1998_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1998_, 0, v_env_1993_);
    lean_ctor_set(v___x_1998_, 1, v_mctx_1995_);
    lean_ctor_set(v___x_1998_, 2, v_lctx_1996_);
    lean_ctor_set(v___x_1998_, 3, v_options_1997_);
    v___x_1999_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1999_, 0, v___x_1998_);
    lean_ctor_set(v___x_1999_, 1, v_msgData_1986_);
    v___x_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2000_, 0, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msgData_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
    lean_dec(v___y_2005_);
    lean_dec_ref(v___y_2004_);
    lean_dec(v___y_2003_);
    lean_dec_ref(v___y_2002_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(
    mut v_opts_2008_: *mut LeanObject,
    mut v_opt_2009_: *mut LeanObject,
) -> u8 {
    let mut v_name_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    v_name_2010_ = lean_ctor_get(v_opt_2009_, 0);
    v_defValue_2011_ = lean_ctor_get(v_opt_2009_, 1);
    v_map_2012_ = lean_ctor_get(v_opts_2008_, 0);
    v___x_2013_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2012_,
            v_name_2010_,
        );
    if lean_obj_tag(v___x_2013_) == 0 {
        let mut v___x_2014_: u8 = 0;
        v___x_2014_ = (lean_unbox(v_defValue_2011_) as u8);
        return v___x_2014_;
    } else {
        let mut v_val_2015_: *mut LeanObject = core::ptr::null_mut();
        v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
        lean_inc(v_val_2015_);
        lean_dec_ref_known(v___x_2013_, 1);
        if lean_obj_tag(v_val_2015_) == 1 {
            let mut v_v_2016_: u8 = 0;
            v_v_2016_ = lean_ctor_get_uint8(v_val_2015_, 0 as u32);
            lean_dec_ref_known(v_val_2015_, 0);
            return v_v_2016_;
        } else {
            let mut v___x_2017_: u8 = 0;
            lean_dec(v_val_2015_);
            v___x_2017_ = (lean_unbox(v_defValue_2011_) as u8);
            return v___x_2017_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9___boxed(
    mut v_opts_2018_: *mut LeanObject,
    mut v_opt_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: u8 = 0;
    let mut v_r_2021_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_opts_2018_, v_opt_2019_);
    lean_dec_ref(v_opt_2019_);
    lean_dec_ref(v_opts_2018_);
    v_r_2021_ = lean_box((v_res_2020_) as usize);
    return v_r_2021_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0()
-> *mut LeanObject {
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2022_ = lean_box(1);
    v___x_2023_ = l_Lean_MessageData_ofFormat(v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3()
-> *mut LeanObject {
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    v___x_2027_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2;
    v___x_2028_ = l_Lean_MessageData_ofFormat(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(
    mut v_x_2029_: *mut LeanObject,
    mut v_x_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v_before_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2030_) == 0 {
                    return v_x_2029_;
                } else {
                    v_head_2031_ = lean_ctor_get(v_x_2030_, 0);
                    v_tail_2032_ = lean_ctor_get(v_x_2030_, 1);
                    v_isSharedCheck_2054_ = (!lean_is_exclusive(v_x_2030_)) as u8;
                    if v_isSharedCheck_2054_ == 0 {
                        v___x_2034_ = v_x_2030_;
                        v_isShared_2035_ = v_isSharedCheck_2054_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2032_);
                        lean_inc(v_head_2031_);
                        lean_dec(v_x_2030_);
                        v___x_2034_ = lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2054_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2036_ = lean_ctor_get(v_head_2031_, 0);
                v_isSharedCheck_2052_ = (!lean_is_exclusive(v_head_2031_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = lean_ctor_get(v_head_2031_, 1);
                    lean_dec(v_unused_2053_);
                    v___x_2038_ = v_head_2031_;
                    v_isShared_2039_ = v_isSharedCheck_2052_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_2036_);
                    lean_dec(v_head_2031_);
                    v___x_2038_ = lean_box(0);
                    v_isShared_2039_ = v_isSharedCheck_2052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2040_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
                if v_isShared_2039_ == 0 {
                    lean_ctor_set_tag(v___x_2038_, 7);
                    lean_ctor_set(v___x_2038_, 1, v___x_2040_);
                    lean_ctor_set(v___x_2038_, 0, v_x_2029_);
                    v___x_2042_ = v___x_2038_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_x_2029_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2040_);
                    v___x_2042_ = v_reuseFailAlloc_2051_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2043_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3);
                if v_isShared_2035_ == 0 {
                    lean_ctor_set_tag(v___x_2034_, 7);
                    lean_ctor_set(v___x_2034_, 1, v___x_2043_);
                    lean_ctor_set(v___x_2034_, 0, v___x_2042_);
                    v___x_2045_ = v___x_2034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2050_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2043_);
                    v___x_2045_ = v_reuseFailAlloc_2050_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2046_ = l_Lean_MessageData_ofSyntax(v_before_2036_);
                v___x_2047_ = l_Lean_indentD(v___x_2046_);
                v___x_2048_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2048_, 0, v___x_2045_);
                lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                v_x_2029_ = v___x_2048_;
                v_x_2030_ = v_tail_2032_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1;
    v___x_2059_ = l_Lean_MessageData_ofFormat(v___x_2058_);
    return v___x_2059_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(
    mut v_msgData_2060_: *mut LeanObject,
    mut v_macroStack_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut v_unused_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2064_ = lean_ctor_get(v___y_2062_, 2);
                v___x_2065_ = l_Lean_Elab_pp_macroStack;
                v___x_2066_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_options_2064_, v___x_2065_);
                if v___x_2066_ == 0 {
                    lean_dec(v_macroStack_2061_);
                    v___x_2067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2067_, 0, v_msgData_2060_);
                    return v___x_2067_;
                } else {
                    if lean_obj_tag(v_macroStack_2061_) == 0 {
                        v___x_2068_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2068_, 0, v_msgData_2060_);
                        return v___x_2068_;
                    } else {
                        v_head_2069_ = lean_ctor_get(v_macroStack_2061_, 0);
                        lean_inc(v_head_2069_);
                        v_after_2070_ = lean_ctor_get(v_head_2069_, 1);
                        v_isSharedCheck_2085_ = (!lean_is_exclusive(v_head_2069_)) as u8;
                        if v_isSharedCheck_2085_ == 0 {
                            v_unused_2086_ = lean_ctor_get(v_head_2069_, 0);
                            lean_dec(v_unused_2086_);
                            v___x_2072_ = v_head_2069_;
                            v_isShared_2073_ = v_isSharedCheck_2085_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_2070_);
                            lean_dec(v_head_2069_);
                            v___x_2072_ = lean_box(0);
                            v_isShared_2073_ = v_isSharedCheck_2085_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2074_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
                if v_isShared_2073_ == 0 {
                    lean_ctor_set_tag(v___x_2072_, 7);
                    lean_ctor_set(v___x_2072_, 1, v___x_2074_);
                    lean_ctor_set(v___x_2072_, 0, v_msgData_2060_);
                    v___x_2076_ = v___x_2072_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_msgData_2060_);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2074_);
                    v___x_2076_ = v_reuseFailAlloc_2084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2077_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2);
                v___x_2078_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2078_, 0, v___x_2076_);
                lean_ctor_set(v___x_2078_, 1, v___x_2077_);
                v___x_2079_ = l_Lean_MessageData_ofSyntax(v_after_2070_);
                v___x_2080_ = l_Lean_indentD(v___x_2079_);
                v_msgData_2081_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_2081_, 0, v___x_2078_);
                lean_ctor_set(v_msgData_2081_, 1, v___x_2080_);
                v___x_2082_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(v_msgData_2081_, v_macroStack_2061_);
                v___x_2083_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2083_, 0, v___x_2082_);
                return v___x_2083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_msgData_2087_: *mut LeanObject,
    mut v_macroStack_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2091_: *mut LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_2087_, v_macroStack_2088_, v___y_2089_);
    lean_dec_ref(v___y_2089_);
    return v_res_2091_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(
    mut v_msg_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2100_ = lean_ctor_get(v___y_2097_, 5);
                v___x_2101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msg_2092_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
                v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
                lean_inc(v_a_2102_);
                lean_dec_ref(v___x_2101_);
                v_macroStack_2103_ = lean_ctor_get(v___y_2093_, 1);
                v___x_2104_ = l_Lean_Elab_getBetterRef(v_ref_2100_, v_macroStack_2103_);
                lean_inc(v_macroStack_2103_);
                v___x_2105_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_a_2102_, v_macroStack_2103_, v___y_2097_);
                v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
                v_isSharedCheck_2114_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                if v_isSharedCheck_2114_ == 0 {
                    v___x_2108_ = v___x_2105_;
                    v_isShared_2109_ = v_isSharedCheck_2114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2106_);
                    lean_dec(v___x_2105_);
                    v___x_2108_ = lean_box(0);
                    v_isShared_2109_ = v_isSharedCheck_2114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2110_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2110_, 0, v___x_2104_);
                lean_ctor_set(v___x_2110_, 1, v_a_2106_);
                if v_isShared_2109_ == 0 {
                    lean_ctor_set_tag(v___x_2108_, 1);
                    lean_ctor_set(v___x_2108_, 0, v___x_2110_);
                    v___x_2112_ = v___x_2108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg___boxed(
    mut v_msg_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
    mut v___y_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2123_: *mut LeanObject = core::ptr::null_mut();
    v_res_2123_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
    lean_dec(v___y_2121_);
    lean_dec_ref(v___y_2120_);
    lean_dec(v___y_2119_);
    lean_dec_ref(v___y_2118_);
    lean_dec(v___y_2117_);
    lean_dec_ref(v___y_2116_);
    return v_res_2123_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2125_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0;
    v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    v___x_2128_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2;
    v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(
    mut v_constName_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: u8 = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2138_ = lean_st_ref_get(v___y_2136_);
                v_env_2139_ = lean_ctor_get(v___x_2138_, 0);
                lean_inc_ref(v_env_2139_);
                lean_dec(v___x_2138_);
                lean_inc(v_constName_2130_);
                v___x_2140_ = l_Lean_isInductiveCore_x3f(v_env_2139_, v_constName_2130_);
                if lean_obj_tag(v___x_2140_) == 0 {
                    v___x_2141_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1);
                    v___x_2142_ = 0;
                    v___x_2143_ = l_Lean_MessageData_ofConstName(v_constName_2130_, v___x_2142_);
                    v___x_2144_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2144_, 0, v___x_2141_);
                    lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                    v___x_2145_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3);
                    v___x_2146_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2146_, 0, v___x_2144_);
                    lean_ctor_set(v___x_2146_, 1, v___x_2145_);
                    v___x_2147_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v___x_2146_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
                    return v___x_2147_;
                } else {
                    lean_dec(v_constName_2130_);
                    v_val_2148_ = lean_ctor_get(v___x_2140_, 0);
                    v_isSharedCheck_2155_ = (!lean_is_exclusive(v___x_2140_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v___x_2150_ = v___x_2140_;
                        v_isShared_2151_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2148_);
                        lean_dec(v___x_2140_);
                        v___x_2150_ = lean_box(0);
                        v_isShared_2151_ = v_isSharedCheck_2155_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2151_ == 0 {
                    lean_ctor_set_tag(v___x_2150_, 0);
                    v___x_2153_ = v___x_2150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_val_2148_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___boxed(
    mut v_constName_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
    mut v___y_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2164_: *mut LeanObject = core::ptr::null_mut();
    v_res_2164_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_constName_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
    lean_dec(v___y_2162_);
    lean_dec_ref(v___y_2161_);
    lean_dec(v___y_2160_);
    lean_dec_ref(v___y_2159_);
    lean_dec(v___y_2158_);
    lean_dec_ref(v___y_2157_);
    return v_res_2164_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(
    mut v_declName_2165_: *mut LeanObject,
    mut v_a_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
    mut v_a_2168_: *mut LeanObject,
    mut v_a_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_2165_);
                v___x_2173_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_declName_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
                if lean_obj_tag(v___x_2173_) == 0 {
                    v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
                    lean_inc(v_a_2174_);
                    lean_dec_ref_known(v___x_2173_, 1);
                    v_toConstantVal_2175_ = lean_ctor_get(v_a_2174_, 0);
                    lean_inc_ref(v_toConstantVal_2175_);
                    v_ctors_2176_ = lean_ctor_get(v_a_2174_, 4);
                    lean_inc(v_ctors_2176_);
                    lean_dec(v_a_2174_);
                    v_type_2177_ = lean_ctor_get(v_toConstantVal_2175_, 2);
                    lean_inc_ref(v_type_2177_);
                    lean_dec_ref(v_toConstantVal_2175_);
                    v___f_2178_ = lean_alloc_closure(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                    lean_closure_set(v___f_2178_, 0, v_ctors_2176_);
                    lean_closure_set(v___f_2178_, 1, v_declName_2165_);
                    v___x_2179_ = 0;
                    v___x_2180_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_2177_, v___f_2178_, v___x_2179_, v___x_2179_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
                    return v___x_2180_;
                } else {
                    lean_dec(v_declName_2165_);
                    v_a_2181_ = lean_ctor_get(v___x_2173_, 0);
                    v_isSharedCheck_2188_ = (!lean_is_exclusive(v___x_2173_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2183_ = v___x_2173_;
                        v_isShared_2184_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2181_);
                        lean_dec(v___x_2173_);
                        v___x_2183_ = lean_box(0);
                        v_isShared_2184_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2184_ == 0 {
                    v___x_2186_ = v___x_2183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed(
    mut v_declName_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2197_: *mut LeanObject = core::ptr::null_mut();
    v_res_2197_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(
        v_declName_2189_,
        v_a_2190_,
        v_a_2191_,
        v_a_2192_,
        v_a_2193_,
        v_a_2194_,
        v_a_2195_,
    );
    lean_dec(v_a_2195_);
    lean_dec_ref(v_a_2194_);
    lean_dec(v_a_2193_);
    lean_dec_ref(v_a_2192_);
    lean_dec(v_a_2191_);
    lean_dec_ref(v_a_2190_);
    return v_res_2197_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(
    mut v_as_2198_: *mut LeanObject,
    mut v_sz_2199_: usize,
    mut v_i_2200_: usize,
    mut v_b_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_2198_, v_sz_2199_, v_i_2200_, v_b_2201_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
    return v___x_2209_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___boxed(
    mut v_as_2210_: *mut LeanObject,
    mut v_sz_2211_: *mut LeanObject,
    mut v_i_2212_: *mut LeanObject,
    mut v_b_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2221_: usize = 0;
    let mut v_i_boxed_2222_: usize = 0;
    let mut v_res_2223_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2211_);
    lean_dec(v_sz_2211_);
    v_i_boxed_2222_ = lean_unbox_usize(v_i_2212_);
    lean_dec(v_i_2212_);
    v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(v_as_2210_, v_sz_boxed_2221_, v_i_boxed_2222_, v_b_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
    lean_dec(v___y_2219_);
    lean_dec_ref(v___y_2218_);
    lean_dec(v___y_2217_);
    lean_dec_ref(v___y_2216_);
    lean_dec(v___y_2215_);
    lean_dec_ref(v___y_2214_);
    lean_dec_ref(v_as_2210_);
    return v_res_2223_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(
    mut v_sz_2224_: usize,
    mut v_i_2225_: usize,
    mut v_bs_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_2224_, v_i_2225_, v_bs_2226_, v___y_2231_);
    return v___x_2234_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___boxed(
    mut v_sz_2235_: *mut LeanObject,
    mut v_i_2236_: *mut LeanObject,
    mut v_bs_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2245_: usize = 0;
    let mut v_i_boxed_2246_: usize = 0;
    let mut v_res_2247_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2235_);
    lean_dec(v_sz_2235_);
    v_i_boxed_2246_ = lean_unbox_usize(v_i_2236_);
    lean_dec(v_i_2236_);
    v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(v_sz_boxed_2245_, v_i_boxed_2246_, v_bs_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
    lean_dec(v___y_2243_);
    lean_dec_ref(v___y_2242_);
    lean_dec(v___y_2241_);
    lean_dec_ref(v___y_2240_);
    lean_dec(v___y_2239_);
    lean_dec_ref(v___y_2238_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(
    mut v_00_u03b1_2248_: *mut LeanObject,
    mut v_msg_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
    return v___x_2257_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___boxed(
    mut v_00_u03b1_2258_: *mut LeanObject,
    mut v_msg_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2267_: *mut LeanObject = core::ptr::null_mut();
    v_res_2267_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(v_00_u03b1_2258_, v_msg_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
    lean_dec(v___y_2265_);
    lean_dec_ref(v___y_2264_);
    lean_dec(v___y_2263_);
    lean_dec_ref(v___y_2262_);
    lean_dec(v___y_2261_);
    lean_dec_ref(v___y_2260_);
    return v_res_2267_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(
    mut v_msgData_2268_: *mut LeanObject,
    mut v_macroStack_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_2268_, v_macroStack_2269_, v___y_2274_);
    return v___x_2277_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___boxed(
    mut v_msgData_2278_: *mut LeanObject,
    mut v_macroStack_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2287_: *mut LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(v_msgData_2278_, v_macroStack_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
    lean_dec(v___y_2285_);
    lean_dec_ref(v___y_2284_);
    lean_dec(v___y_2283_);
    lean_dec_ref(v___y_2282_);
    lean_dec(v___y_2281_);
    lean_dec_ref(v___y_2280_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(
    mut v_declName_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v___x_2291_ = lean_st_ref_get(v___y_2289_);
    v_env_2292_ = lean_ctor_get(v___x_2291_, 0);
    lean_inc_ref(v_env_2292_);
    lean_dec(v___x_2291_);
    v___x_2293_ = l_Lean_isInductiveCore(v_env_2292_, v_declName_2288_);
    v___x_2294_ = lean_box((v___x_2293_) as usize);
    v___x_2295_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2295_, 0, v___x_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg___boxed(
    mut v_declName_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
    v_res_2299_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(
            v_declName_2296_,
            v___y_2297_,
        );
    lean_dec(v___y_2297_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(
    mut v_declName_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(
            v_declName_2300_,
            v___y_2302_,
        );
    return v___x_2304_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___boxed(
    mut v_declName_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2309_: *mut LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(
        v_declName_2305_,
        v___y_2306_,
        v___y_2307_,
    );
    lean_dec(v___y_2307_);
    lean_dec_ref(v___y_2306_);
    return v_res_2309_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(
    mut v_____do__lift_2310_: u8,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_2310_ == 0 {
        let mut v___x_2314_: u8 = 0;
        let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
        v___x_2314_ = 1;
        v___x_2315_ = lean_box((v___x_2314_) as usize);
        v___x_2316_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2316_, 0, v___x_2315_);
        return v___x_2316_;
    } else {
        let mut v___x_2317_: u8 = 0;
        let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
        v___x_2317_ = 0;
        v___x_2318_ = lean_box((v___x_2317_) as usize);
        v___x_2319_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2319_, 0, v___x_2318_);
        return v___x_2319_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0___boxed(
    mut v_____do__lift_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_1888__boxed_2324_: u8 = 0;
    let mut v_res_2325_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_1888__boxed_2324_ = (lean_unbox(v_____do__lift_2320_) as u8);
    v_res_2325_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(
        v_____do__lift_1888__boxed_2324_,
        v___y_2321_,
        v___y_2322_,
    );
    lean_dec(v___y_2322_);
    lean_dec_ref(v___y_2321_);
    return v_res_2325_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(
    mut v_as_2326_: *mut LeanObject,
    mut v_i_2327_: usize,
    mut v_stop_2328_: usize,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: u8 = 0;
    let mut v_a_2335_: u8 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2332_ = lean_usize_dec_eq(v_i_2327_, v_stop_2328_);
                if v___x_2332_ == 0 {
                    v___x_2333_ = 1;
                    v___x_2341_ = lean_array_uget_borrowed(v_as_2326_, v_i_2327_);
                    lean_inc(v___x_2341_);
                    v___x_2342_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v___x_2341_, v___y_2330_);
                    if lean_obj_tag(v___x_2342_) == 0 {
                        v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
                        v_isSharedCheck_2352_ = (!lean_is_exclusive(v___x_2342_)) as u8;
                        if v_isSharedCheck_2352_ == 0 {
                            v___x_2345_ = v___x_2342_;
                            v_isShared_2346_ = v_isSharedCheck_2352_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2343_);
                            lean_dec(v___x_2342_);
                            v___x_2345_ = lean_box(0);
                            v_isShared_2346_ = v_isSharedCheck_2352_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_2342_) == 0 {
                            v_a_2353_ = lean_ctor_get(v___x_2342_, 0);
                            lean_inc(v_a_2353_);
                            lean_dec_ref_known(v___x_2342_, 1);
                            v___x_2354_ = (lean_unbox(v_a_2353_) as u8);
                            lean_dec(v_a_2353_);
                            v_a_2335_ = v___x_2354_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2342_;
                        }
                    }
                } else {
                    v___x_2355_ = 0;
                    v___x_2356_ = lean_box((v___x_2355_) as usize);
                    v___x_2357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2357_, 0, v___x_2356_);
                    return v___x_2357_;
                }
            }
            1 => {
                if v_a_2335_ == 0 {
                    v___x_2336_ = 1usize;
                    v___x_2337_ = lean_usize_add(v_i_2327_, v___x_2336_);
                    v_i_2327_ = v___x_2337_;
                    state = 0;
                    continue;
                } else {
                    v___x_2339_ = lean_box((v___x_2333_) as usize);
                    v___x_2340_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2340_, 0, v___x_2339_);
                    return v___x_2340_;
                }
            }
            2 => {
                v___x_2347_ = (lean_unbox(v_a_2343_) as u8);
                lean_dec(v_a_2343_);
                if v___x_2347_ == 0 {
                    v___x_2348_ = lean_box((v___x_2333_) as usize);
                    if v_isShared_2346_ == 0 {
                        lean_ctor_set(v___x_2345_, 0, v___x_2348_);
                        v___x_2350_ = v___x_2345_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
                        v___x_2350_ = v_reuseFailAlloc_2351_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2345_);
                    v_a_2335_ = v___x_2332_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2___boxed(
    mut v_as_2358_: *mut LeanObject,
    mut v_i_2359_: *mut LeanObject,
    mut v_stop_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2364_: usize = 0;
    let mut v_stop_boxed_2365_: usize = 0;
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2364_ = lean_unbox_usize(v_i_2359_);
    lean_dec(v_i_2359_);
    v_stop_boxed_2365_ = lean_unbox_usize(v_stop_2360_);
    lean_dec(v_stop_2360_);
    v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_as_2358_, v_i_boxed_2364_, v_stop_boxed_2365_, v___y_2361_, v___y_2362_);
    lean_dec(v___y_2362_);
    lean_dec_ref(v___y_2361_);
    lean_dec_ref(v_as_2358_);
    return v_res_2366_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(
    mut v___x_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2371_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___x_2367_,
                    v___y_2368_,
                    v___y_2369_,
                );
                if lean_obj_tag(v___x_2371_) == 0 {
                    v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
                    lean_inc(v_a_2372_);
                    lean_dec_ref_known(v___x_2371_, 1);
                    v___x_2373_ =
                        l_Lean_Elab_Command_elabCommand(v_a_2372_, v___y_2368_, v___y_2369_);
                    return v___x_2373_;
                } else {
                    v_a_2374_ = lean_ctor_get(v___x_2371_, 0);
                    v_isSharedCheck_2381_ = (!lean_is_exclusive(v___x_2371_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2376_ = v___x_2371_;
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2374_);
                        lean_dec(v___x_2371_);
                        v___x_2376_ = lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2377_ == 0 {
                    v___x_2379_ = v___x_2376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed(
    mut v___x_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(v___x_2382_, v___y_2383_, v___y_2384_);
    lean_dec(v___y_2384_);
    lean_dec_ref(v___y_2383_);
    return v_res_2386_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(
    mut v_as_2387_: *mut LeanObject,
    mut v_sz_2388_: usize,
    mut v_i_2389_: usize,
    mut v_b_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2394_ = lean_usize_dec_lt(v_i_2389_, v_sz_2388_);
                if v___x_2394_ == 0 {
                    v___x_2395_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2395_, 0, v_b_2390_);
                    return v___x_2395_;
                } else {
                    v_a_2396_ = lean_array_uget_borrowed(v_as_2387_, v_i_2389_);
                    lean_inc_n(v_a_2396_, 2);
                    v___x_2397_ = lean_alloc_closure(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed as *mut core::ffi::c_void, 8, 1);
                    lean_closure_set(v___x_2397_, 0, v_a_2396_);
                    v___f_2398_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    lean_closure_set(v___f_2398_, 0, v___x_2397_);
                    v___x_2399_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
                        v_a_2396_,
                        v___f_2398_,
                        v___y_2391_,
                        v___y_2392_,
                    );
                    if lean_obj_tag(v___x_2399_) == 0 {
                        lean_dec_ref_known(v___x_2399_, 1);
                        v___x_2400_ = lean_box(0);
                        v___x_2401_ = 1usize;
                        v___x_2402_ = lean_usize_add(v_i_2389_, v___x_2401_);
                        v_i_2389_ = v___x_2402_;
                        v_b_2390_ = v___x_2400_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2399_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___boxed(
    mut v_as_2404_: *mut LeanObject,
    mut v_sz_2405_: *mut LeanObject,
    mut v_i_2406_: *mut LeanObject,
    mut v_b_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2411_: usize = 0;
    let mut v_i_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2405_);
    lean_dec(v_sz_2405_);
    v_i_boxed_2412_ = lean_unbox_usize(v_i_2406_);
    lean_dec(v_i_2406_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_as_2404_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2407_, v___y_2408_, v___y_2409_);
    lean_dec(v___y_2409_);
    lean_dec_ref(v___y_2408_);
    lean_dec_ref(v_as_2404_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(
    mut v_declNames_2414_: *mut LeanObject,
    mut v_a_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2420_: usize = 0;
    let mut v___x_2421_: usize = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_unused_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: usize = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = lean_unsigned_to_nat(0);
                v___x_2446_ = lean_array_get_size(v_declNames_2414_);
                v___x_2447_ = lean_nat_dec_lt(v___x_2445_, v___x_2446_);
                if v___x_2447_ == 0 {
                    v___x_2448_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(
                        v___x_2447_,
                        v_a_2415_,
                        v_a_2416_,
                    );
                    v___y_2442_ = v___x_2448_;
                    state = 6;
                    continue;
                } else {
                    if v___x_2447_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2449_ = 0usize;
                        v___x_2450_ = lean_usize_of_nat(v___x_2446_);
                        v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_declNames_2414_, v___x_2449_, v___x_2450_, v_a_2415_, v_a_2416_);
                        if lean_obj_tag(v___x_2451_) == 0 {
                            v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
                            lean_inc(v_a_2452_);
                            lean_dec_ref_known(v___x_2451_, 1);
                            v___x_2453_ = (lean_unbox(v_a_2452_) as u8);
                            lean_dec(v_a_2452_);
                            v___x_2454_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(
                                v___x_2453_,
                                v_a_2415_,
                                v_a_2416_,
                            );
                            v___y_2442_ = v___x_2454_;
                            state = 6;
                            continue;
                        } else {
                            v___y_2442_ = v___x_2451_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2419_ = lean_box(0);
                v_sz_2420_ = lean_array_size(v_declNames_2414_);
                v___x_2421_ = 0usize;
                v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_declNames_2414_, v_sz_2420_, v___x_2421_, v___x_2419_, v_a_2415_, v_a_2416_);
                if lean_obj_tag(v___x_2422_) == 0 {
                    v_isSharedCheck_2431_ = (!lean_is_exclusive(v___x_2422_)) as u8;
                    if v_isSharedCheck_2431_ == 0 {
                        v_unused_2432_ = lean_ctor_get(v___x_2422_, 0);
                        lean_dec(v_unused_2432_);
                        v___x_2424_ = v___x_2422_;
                        v_isShared_2425_ = v_isSharedCheck_2431_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2422_);
                        v___x_2424_ = lean_box(0);
                        v_isShared_2425_ = v_isSharedCheck_2431_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2433_ = lean_ctor_get(v___x_2422_, 0);
                    v_isSharedCheck_2440_ = (!lean_is_exclusive(v___x_2422_)) as u8;
                    if v_isSharedCheck_2440_ == 0 {
                        v___x_2435_ = v___x_2422_;
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2433_);
                        lean_dec(v___x_2422_);
                        v___x_2435_ = lean_box(0);
                        v_isShared_2436_ = v_isSharedCheck_2440_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2426_ = 1;
                v___x_2427_ = lean_box((v___x_2426_) as usize);
                if v_isShared_2425_ == 0 {
                    lean_ctor_set(v___x_2424_, 0, v___x_2427_);
                    v___x_2429_ = v___x_2424_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
                    v___x_2429_ = v_reuseFailAlloc_2430_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2429_;
            }
            4 => {
                if v_isShared_2436_ == 0 {
                    v___x_2438_ = v___x_2435_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
                    v___x_2438_ = v_reuseFailAlloc_2439_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2438_;
            }
            6 => {
                if lean_obj_tag(v___y_2442_) == 0 {
                    v_a_2443_ = lean_ctor_get(v___y_2442_, 0);
                    v___x_2444_ = (lean_unbox(v_a_2443_) as u8);
                    if v___x_2444_ == 0 {
                        return v___y_2442_;
                    } else {
                        lean_dec_ref_known(v___y_2442_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_2442_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed(
    mut v_declNames_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2459_: *mut LeanObject = core::ptr::null_mut();
    v_res_2459_ =
        l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(v_declNames_2455_, v_a_2456_, v_a_2457_);
    lean_dec(v_a_2457_);
    lean_dec_ref(v_a_2456_);
    lean_dec_ref(v_declNames_2455_);
    return v_res_2459_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13;
    v___x_2463_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_;
    v___x_2464_ = l_Lean_Elab_registerDerivingHandler(v___x_2462_, v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2____boxed(
    mut v_a_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
    return v_res_2466_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_Nonempty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_Nonempty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Deriving_Nonempty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Nonempty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_Nonempty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_Nonempty(builtin);
}
