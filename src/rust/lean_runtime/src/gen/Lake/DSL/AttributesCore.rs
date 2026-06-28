// Lean compiler output
// Module: Lake.DSL.AttributesCore
// Imports: Lake.Util.OrderedTagAttribute
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lake::Util::OrderedTagAttribute::{
    initialize_Lake_Util_OrderedTagAttribute, l_Lake_OrderedTagAttribute_hasTag,
    l_Lake_registerOrderedTagAttribute, runtime_initialize_Lake_Util_OrderedTagAttribute,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 97, 99, 107, 97, 103, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,6671755061125946191 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 99, 107, 97, 103, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,659528549093005558 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 99, 107, 97, 103, 101, 95, 100, 101, 112, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject,4808916106510604781 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 97, 99, 107, 97, 103, 101, 68, 101, 112, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject,2574662391088497709 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject,985716791886485019 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 112, 111, 115, 116, 45, 117, 112, 100, 97, 116, 101, 32, 104, 111, 111, 107, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject,12436946493679816533 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject,887671011676595348 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject,14767982047059385626 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 100, 101, 102, 97, 117, 108, 116, 95, 115, 99, 114, 105, 112, 116, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 102, 97, 117, 108, 116, 95, 115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject,16430358650169544679 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 32, 97, 115, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 83, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject,758561379943963750 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject,12295998048739818339 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 76, 101, 97, 110, 32, 108, 105, 98, 114, 97, 114, 121, 32, 116, 97, 114, 103, 101, 116, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject,7818855776703404064 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject,10587356296225942211 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: LeanStringObject<65> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 76, 101, 97, 110, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 69, 120, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject,11424057956103599804 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject,11562366611225967008 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 101, 120, 116, 101, 114, 110, 97, 108, 32, 108, 105, 98, 114, 97, 114, 121, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 116, 101, 114, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject,7509421779037782117 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject,4067501922346325234 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 105, 110, 112, 117, 116, 32, 102, 105, 108, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 112, 117, 116, 70, 105, 108, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject,17885622076320419789 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject,9710019104504222840 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 105, 110, 112, 117, 116, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 112, 117, 116, 68, 105, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject,12085934795154313082 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject,6124717609876119291 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject,9199123000070154982 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanStringObject<87> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 100, 101, 102, 97, 117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 116, 97, 114, 103, 101, 116, 32, 40, 101, 46, 103, 46, 44, 32, 96, 108, 101, 97, 110, 95, 108, 105, 98, 96, 44, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 41, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 102, 97, 117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject,12969074616217864974 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 116, 97, 114, 103, 101, 116, 32, 97, 115, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 84, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject,8325663718235124360 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanStringObject<82> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 44, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 44, 32, 111, 114, 32, 96, 108, 101, 97, 110, 95, 108, 105, 98, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject,2705511379774931411 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 44, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 44, 32, 111, 114, 32, 108, 105, 98, 114, 97, 114, 121, 32, 97, 115, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 116, 101, 115, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 115, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject,1466235757312191377 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 32, 111, 114, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject,11055114253656833314 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 32, 111, 114, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 97, 115, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 105, 110, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject,12055850808226400418 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 111, 100, 117, 108, 101, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject,9448625530981317401 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 109, 111, 100, 117, 108, 101, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [109, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject,11171157541301760440 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 99, 107, 97, 103, 101, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject,9378971393347028642 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject,18143559972510357022 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 98, 114, 97, 114, 121, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject,17310535023809783662 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 108, 105, 98, 114, 97, 114, 121, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject,3952046105223012164 as *mut LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(
    mut v_x_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_606_ = lean_box(0);
    v___x_607_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_607_, 0, v___x_606_);
    return v___x_607_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(
    mut v_x_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_612_: *mut LeanObject = core::ptr::null_mut();
    v_res_612_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(v_x_608_, v___y_609_, v___y_610_);
    lean_dec(v___y_610_);
    lean_dec_ref(v___y_609_);
    lean_dec(v_x_608_);
    return v_res_612_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v___f_624_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_625_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_626_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_627_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_628_ = l_Lake_registerOrderedTagAttribute(v___x_625_, v___x_626_, v___f_624_, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(
    mut v_a_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_res_630_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
    return v_res_630_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    v___f_640_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_641_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_642_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_643_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_644_ = l_Lake_registerOrderedTagAttribute(v___x_641_, v___x_642_, v___f_640_, v___x_643_);
    return v___x_644_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2____boxed(
    mut v_a_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_646_: *mut LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
    return v_res_646_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    v___f_656_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_657_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_658_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_659_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_660_ = l_Lake_registerOrderedTagAttribute(v___x_657_, v___x_658_, v___f_656_, v___x_659_);
    return v___x_660_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2____boxed(
    mut v_a_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_662_: *mut LeanObject = core::ptr::null_mut();
    v_res_662_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
    return v_res_662_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___f_672_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_673_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_674_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_675_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_676_ = l_Lake_registerOrderedTagAttribute(v___x_673_, v___x_674_, v___f_672_, v___x_675_);
    return v___x_676_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2____boxed(
    mut v_a_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_678_: *mut LeanObject = core::ptr::null_mut();
    v_res_678_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
    return v_res_678_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(
    mut v_a_679_: *mut LeanObject,
    mut v_f_680_: *mut LeanObject,
    mut v___y_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_a_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_697_: u8 = 0;
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_682_);
                lean_inc_ref(v___y_681_);
                v___x_684_ = lean_apply_3(v_a_679_, v___y_681_, v___y_682_, lean_box(0));
                if lean_obj_tag(v___x_684_) == 0 {
                    v_a_685_ = lean_ctor_get(v___x_684_, 0);
                    v_isSharedCheck_693_ = (!lean_is_exclusive(v___x_684_)) as u8;
                    if v_isSharedCheck_693_ == 0 {
                        v___x_687_ = v___x_684_;
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_685_);
                        lean_dec(v___x_684_);
                        v___x_687_ = lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_680_);
                    v_a_694_ = lean_ctor_get(v___x_684_, 0);
                    v_isSharedCheck_701_ = (!lean_is_exclusive(v___x_684_)) as u8;
                    if v_isSharedCheck_701_ == 0 {
                        v___x_696_ = v___x_684_;
                        v_isShared_697_ = v_isSharedCheck_701_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_694_);
                        lean_dec(v___x_684_);
                        v___x_696_ = lean_box(0);
                        v_isShared_697_ = v_isSharedCheck_701_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_689_ = lean_apply_1(v_f_680_, v_a_685_);
                if v_isShared_688_ == 0 {
                    lean_ctor_set(v___x_687_, 0, v___x_689_);
                    v___x_691_ = v___x_687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_691_;
            }
            3 => {
                if v_isShared_697_ == 0 {
                    v___x_699_ = v___x_696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
                    v___x_699_ = v_reuseFailAlloc_700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_a_702_: *mut LeanObject,
    mut v_f_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_707_: *mut LeanObject = core::ptr::null_mut();
    v_res_707_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_702_, v_f_703_, v___y_704_, v___y_705_);
    lean_dec(v___y_705_);
    lean_dec_ref(v___y_704_);
    return v_res_707_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_708_: *mut LeanObject,
    mut v_00_u03b2_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
    mut v_f_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_710_, v_f_711_, v___y_712_, v___y_713_);
    return v___x_715_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_716_: *mut LeanObject,
    mut v_00_u03b2_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_f_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
    mut v___y_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_723_: *mut LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(v_00_u03b1_716_, v_00_u03b2_717_, v_a_718_, v_f_719_, v___y_720_, v___y_721_);
    lean_dec(v___y_721_);
    lean_dec_ref(v___y_720_);
    return v_res_723_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = lean_st_ref_get(v___y_725_);
    v_env_728_ = lean_ctor_get(v___x_727_, 0);
    lean_inc_ref(v_env_728_);
    lean_dec(v___x_727_);
    v___x_729_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_729_, 0, v_env_728_);
    return v___x_729_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v___y_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_733_: *mut LeanObject = core::ptr::null_mut();
    v_res_733_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___y_730_, v___y_731_);
    lean_dec(v___y_731_);
    lean_dec_ref(v___y_730_);
    return v_res_733_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v_name_734_: *mut LeanObject,
    mut v_x_735_: *mut LeanObject,
) -> u8 {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    v___x_736_ = l_Lake_scriptAttr;
    v___x_737_ = l_Lake_OrderedTagAttribute_hasTag(v___x_736_, v_x_735_, v_name_734_);
    return v___x_737_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v_name_738_: *mut LeanObject,
    mut v_x_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_740_: u8 = 0;
    let mut v_r_741_: *mut LeanObject = core::ptr::null_mut();
    v_res_740_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v_name_738_, v_x_739_);
    lean_dec(v_name_738_);
    v_r_741_ = lean_box((v_res_740_) as usize);
    return v_r_741_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0);
    v___x_744_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_744_, 0, v___x_743_);
    return v___x_744_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    v___x_745_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
    v___x_746_ = lean_unsigned_to_nat(0);
    v___x_747_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_747_, 0, v___x_746_);
    lean_ctor_set(v___x_747_, 1, v___x_746_);
    lean_ctor_set(v___x_747_, 2, v___x_746_);
    lean_ctor_set(v___x_747_, 3, v___x_746_);
    lean_ctor_set(v___x_747_, 4, v___x_745_);
    lean_ctor_set(v___x_747_, 5, v___x_745_);
    lean_ctor_set(v___x_747_, 6, v___x_745_);
    lean_ctor_set(v___x_747_, 7, v___x_745_);
    lean_ctor_set(v___x_747_, 8, v___x_745_);
    lean_ctor_set(v___x_747_, 9, v___x_745_);
    return v___x_747_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    v___x_748_ = lean_unsigned_to_nat(32);
    v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
    v___x_750_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_750_, 0, v___x_749_);
    return v___x_750_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_751_: usize = 0;
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_751_ = 5usize;
    v___x_752_ = lean_unsigned_to_nat(0);
    v___x_753_ = lean_unsigned_to_nat(32);
    v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
    v___x_755_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3);
    v___x_756_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_756_, 0, v___x_755_);
    lean_ctor_set(v___x_756_, 1, v___x_754_);
    lean_ctor_set(v___x_756_, 2, v___x_752_);
    lean_ctor_set(v___x_756_, 3, v___x_752_);
    lean_ctor_set_usize(v___x_756_, 4, v___x_751_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = lean_box(1);
    v___x_758_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4);
    v___x_759_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
    v___x_760_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_760_, 0, v___x_759_);
    lean_ctor_set(v___x_760_, 1, v___x_758_);
    lean_ctor_set(v___x_760_, 2, v___x_757_);
    return v___x_760_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(
    mut v_msgData_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_st_ref_get(v___y_763_);
    v_env_766_ = lean_ctor_get(v___x_765_, 0);
    lean_inc_ref(v_env_766_);
    lean_dec(v___x_765_);
    v_options_767_ = lean_ctor_get(v___y_762_, 2);
    v___x_768_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2);
    v___x_769_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5);
    lean_inc_ref(v_options_767_);
    v___x_770_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_770_, 0, v_env_766_);
    lean_ctor_set(v___x_770_, 1, v___x_768_);
    lean_ctor_set(v___x_770_, 2, v___x_769_);
    lean_ctor_set(v___x_770_, 3, v_options_767_);
    v___x_771_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_771_, 0, v___x_770_);
    lean_ctor_set(v___x_771_, 1, v_msgData_761_);
    v___x_772_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_msgData_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_777_: *mut LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msgData_773_, v___y_774_, v___y_775_);
    lean_dec(v___y_775_);
    lean_dec_ref(v___y_774_);
    return v_res_777_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_782_ = lean_ctor_get(v___y_779_, 5);
                v___x_783_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msg_778_, v___y_779_, v___y_780_);
                v_a_784_ = lean_ctor_get(v___x_783_, 0);
                v_isSharedCheck_792_ = (!lean_is_exclusive(v___x_783_)) as u8;
                if v_isSharedCheck_792_ == 0 {
                    v___x_786_ = v___x_783_;
                    v_isShared_787_ = v_isSharedCheck_792_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_784_);
                    lean_dec(v___x_783_);
                    v___x_786_ = lean_box(0);
                    v_isShared_787_ = v_isSharedCheck_792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_782_);
                v___x_788_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_788_, 0, v_ref_782_);
                lean_ctor_set(v___x_788_, 1, v_a_784_);
                if v_isShared_787_ == 0 {
                    lean_ctor_set_tag(v___x_786_, 1);
                    lean_ctor_set(v___x_786_, 0, v___x_788_);
                    v___x_790_ = v___x_786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
                    v___x_790_ = v_reuseFailAlloc_791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
    mut v___y_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_793_, v___y_794_, v___y_795_);
    lean_dec(v___y_795_);
    lean_dec_ref(v___y_794_);
    return v_res_797_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
    return v___x_800_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v___f_801_: *mut LeanObject,
    mut v_name_802_: *mut LeanObject,
    mut v___y_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_811_: u8 = 0;
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_806_ = lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_806_, 0, v_name_802_);
                v___x_807_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_801_, v___f_806_, v___y_803_, v___y_804_);
                if lean_obj_tag(v___x_807_) == 0 {
                    v_a_808_ = lean_ctor_get(v___x_807_, 0);
                    v_isSharedCheck_819_ = (!lean_is_exclusive(v___x_807_)) as u8;
                    if v_isSharedCheck_819_ == 0 {
                        v___x_810_ = v___x_807_;
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_808_);
                        lean_dec(v___x_807_);
                        v___x_810_ = lean_box(0);
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_820_ = lean_ctor_get(v___x_807_, 0);
                    v_isSharedCheck_827_ = (!lean_is_exclusive(v___x_807_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v___x_822_ = v___x_807_;
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_820_);
                        lean_dec(v___x_807_);
                        v___x_822_ = lean_box(0);
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_812_ = (lean_unbox(v_a_808_) as u8);
                lean_dec(v_a_808_);
                if v___x_812_ == 0 {
                    lean_del_object(v___x_810_);
                    v___x_813_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_);
                    v___x_814_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_813_, v___y_803_, v___y_804_);
                    return v___x_814_;
                } else {
                    v___x_815_ = lean_box(0);
                    if v_isShared_811_ == 0 {
                        lean_ctor_set(v___x_810_, 0, v___x_815_);
                        v___x_817_ = v___x_810_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
                        v___x_817_ = v_reuseFailAlloc_818_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_817_;
            }
            3 => {
                if v_isShared_823_ == 0 {
                    v___x_825_ = v___x_822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
                    v___x_825_ = v_reuseFailAlloc_826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v___f_828_: *mut LeanObject,
    mut v_name_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_833_: *mut LeanObject = core::ptr::null_mut();
    v_res_833_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___f_828_, v_name_829_, v___y_830_, v___y_831_);
    lean_dec(v___y_831_);
    lean_dec_ref(v___y_830_);
    return v_res_833_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    v___f_846_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_847_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_848_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_849_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_850_ = l_Lake_registerOrderedTagAttribute(v___x_847_, v___x_848_, v___f_846_, v___x_849_);
    return v___x_850_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v_a_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_852_: *mut LeanObject = core::ptr::null_mut();
    v_res_852_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
    return v_res_852_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_853_: *mut LeanObject,
    mut v_msg_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_854_, v___y_855_, v___y_856_);
    return v___x_858_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_859_: *mut LeanObject,
    mut v_msg_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_864_: *mut LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(v_00_u03b1_859_, v_msg_860_, v___y_861_, v___y_862_);
    lean_dec(v___y_862_);
    lean_dec_ref(v___y_861_);
    return v_res_864_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___f_874_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_875_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_876_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_877_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_878_ = l_Lake_registerOrderedTagAttribute(v___x_875_, v___x_876_, v___f_874_, v___x_877_);
    return v___x_878_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2____boxed(
    mut v_a_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_880_: *mut LeanObject = core::ptr::null_mut();
    v_res_880_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
    return v_res_880_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    v___f_890_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_891_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_892_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_893_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_894_ = l_Lake_registerOrderedTagAttribute(v___x_891_, v___x_892_, v___f_890_, v___x_893_);
    return v___x_894_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2____boxed(
    mut v_a_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_896_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
    return v_res_896_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___f_906_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_907_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_908_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_909_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_910_ = l_Lake_registerOrderedTagAttribute(v___x_907_, v___x_908_, v___f_906_, v___x_909_);
    return v___x_910_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2____boxed(
    mut v_a_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_912_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
    return v_res_912_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___f_922_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_923_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_924_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_925_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_926_ = l_Lake_registerOrderedTagAttribute(v___x_923_, v___x_924_, v___f_922_, v___x_925_);
    return v___x_926_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2____boxed(
    mut v_a_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_928_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
    return v_res_928_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___f_938_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_939_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_940_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_941_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_942_ = l_Lake_registerOrderedTagAttribute(v___x_939_, v___x_940_, v___f_938_, v___x_941_);
    return v___x_942_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2____boxed(
    mut v_a_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_944_: *mut LeanObject = core::ptr::null_mut();
    v_res_944_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
    return v_res_944_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    v___f_954_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_955_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_956_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_957_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_958_ = l_Lake_registerOrderedTagAttribute(v___x_955_, v___x_956_, v___f_954_, v___x_957_);
    return v___x_958_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2____boxed(
    mut v_a_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_960_: *mut LeanObject = core::ptr::null_mut();
    v_res_960_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
    return v_res_960_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(
    mut v_name_961_: *mut LeanObject,
    mut v_env_962_: *mut LeanObject,
) -> u8 {
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    v___x_963_ = l_Lake_targetAttr;
    v___x_964_ = l_Lake_OrderedTagAttribute_hasTag(v___x_963_, v_env_962_, v_name_961_);
    return v___x_964_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v_name_965_: *mut LeanObject,
    mut v_env_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_967_: u8 = 0;
    let mut v_r_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_967_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v_name_965_, v_env_966_);
    lean_dec(v_name_965_);
    v_r_968_ = lean_box((v_res_967_) as usize);
    return v_r_968_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    v___x_970_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
    return v___x_971_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(
    mut v___f_972_: *mut LeanObject,
    mut v_name_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_977_ = lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_977_, 0, v_name_973_);
                v___x_978_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_972_, v___f_977_, v___y_974_, v___y_975_);
                if lean_obj_tag(v___x_978_) == 0 {
                    v_a_979_ = lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_990_ = (!lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_990_ == 0 {
                        v___x_981_ = v___x_978_;
                        v_isShared_982_ = v_isSharedCheck_990_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_979_);
                        lean_dec(v___x_978_);
                        v___x_981_ = lean_box(0);
                        v_isShared_982_ = v_isSharedCheck_990_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_991_ = lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_998_ = (!lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_993_ = v___x_978_;
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_991_);
                        lean_dec(v___x_978_);
                        v___x_993_ = lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_983_ = (lean_unbox(v_a_979_) as u8);
                lean_dec(v_a_979_);
                if v___x_983_ == 0 {
                    lean_del_object(v___x_981_);
                    v___x_984_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_);
                    v___x_985_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_984_, v___y_974_, v___y_975_);
                    return v___x_985_;
                } else {
                    v___x_986_ = lean_box(0);
                    if v_isShared_982_ == 0 {
                        lean_ctor_set(v___x_981_, 0, v___x_986_);
                        v___x_988_ = v___x_981_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
                        v___x_988_ = v_reuseFailAlloc_989_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_988_;
            }
            3 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v___f_999_: *mut LeanObject,
    mut v_name_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_res_1004_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v___f_999_, v_name_1000_, v___y_1001_, v___y_1002_);
    lean_dec(v___y_1002_);
    lean_dec_ref(v___y_1001_);
    return v_res_1004_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    v___f_1016_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1017_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1018_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1019_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1020_ =
        l_Lake_registerOrderedTagAttribute(v___x_1017_, v___x_1018_, v___f_1016_, v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v_a_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1022_: *mut LeanObject = core::ptr::null_mut();
    v_res_1022_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
    return v_res_1022_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(
    mut v_name_1023_: *mut LeanObject,
    mut v_env_1024_: *mut LeanObject,
) -> u8 {
    let mut v___y_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1029_ = l_Lake_scriptAttr;
                lean_inc_ref(v_env_1024_);
                v___x_1030_ =
                    l_Lake_OrderedTagAttribute_hasTag(v___x_1029_, v_env_1024_, v_name_1023_);
                if v___x_1030_ == 0 {
                    v___x_1031_ = l_Lake_leanExeAttr;
                    lean_inc_ref(v_env_1024_);
                    v___x_1032_ =
                        l_Lake_OrderedTagAttribute_hasTag(v___x_1031_, v_env_1024_, v_name_1023_);
                    v___y_1026_ = v___x_1032_;
                    state = 1;
                    continue;
                } else {
                    v___y_1026_ = v___x_1030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1026_ == 0 {
                    v___x_1027_ = l_Lake_leanLibAttr;
                    v___x_1028_ =
                        l_Lake_OrderedTagAttribute_hasTag(v___x_1027_, v_env_1024_, v_name_1023_);
                    return v___x_1028_;
                } else {
                    lean_dec_ref(v_env_1024_);
                    return v___y_1026_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v_name_1033_: *mut LeanObject,
    mut v_env_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v_name_1033_, v_env_1034_);
    lean_dec(v_name_1033_);
    v_r_1036_ = lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(
    mut v___f_1040_: *mut LeanObject,
    mut v_name_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
    mut v___y_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_a_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1045_ = lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1045_, 0, v_name_1041_);
                v___x_1046_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_1040_, v___f_1045_, v___y_1042_, v___y_1043_);
                if lean_obj_tag(v___x_1046_) == 0 {
                    v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
                    v_isSharedCheck_1058_ = (!lean_is_exclusive(v___x_1046_)) as u8;
                    if v_isSharedCheck_1058_ == 0 {
                        v___x_1049_ = v___x_1046_;
                        v_isShared_1050_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1047_);
                        lean_dec(v___x_1046_);
                        v___x_1049_ = lean_box(0);
                        v_isShared_1050_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1059_ = lean_ctor_get(v___x_1046_, 0);
                    v_isSharedCheck_1066_ = (!lean_is_exclusive(v___x_1046_)) as u8;
                    if v_isSharedCheck_1066_ == 0 {
                        v___x_1061_ = v___x_1046_;
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1059_);
                        lean_dec(v___x_1046_);
                        v___x_1061_ = lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1051_ = (lean_unbox(v_a_1047_) as u8);
                lean_dec(v_a_1047_);
                if v___x_1051_ == 0 {
                    lean_del_object(v___x_1049_);
                    v___x_1052_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_);
                    v___x_1053_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_1052_, v___y_1042_, v___y_1043_);
                    return v___x_1053_;
                } else {
                    v___x_1054_ = lean_box(0);
                    if v_isShared_1050_ == 0 {
                        lean_ctor_set(v___x_1049_, 0, v___x_1054_);
                        v___x_1056_ = v___x_1049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                        v___x_1056_ = v_reuseFailAlloc_1057_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1056_;
            }
            3 => {
                if v_isShared_1062_ == 0 {
                    v___x_1064_ = v___x_1061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
                    v___x_1064_ = v_reuseFailAlloc_1065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v___f_1067_: *mut LeanObject,
    mut v_name_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
    mut v___y_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1072_: *mut LeanObject = core::ptr::null_mut();
    v_res_1072_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v___f_1067_, v_name_1068_, v___y_1069_, v___y_1070_);
    lean_dec(v___y_1070_);
    lean_dec_ref(v___y_1069_);
    return v_res_1072_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    v___f_1084_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1085_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1086_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1087_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1088_ =
        l_Lake_registerOrderedTagAttribute(v___x_1085_, v___x_1086_, v___f_1084_, v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v_a_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1090_: *mut LeanObject = core::ptr::null_mut();
    v_res_1090_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
    return v_res_1090_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(
    mut v_name_1091_: *mut LeanObject,
    mut v_env_1092_: *mut LeanObject,
) -> u8 {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    v___x_1093_ = l_Lake_scriptAttr;
    lean_inc_ref(v_env_1092_);
    v___x_1094_ = l_Lake_OrderedTagAttribute_hasTag(v___x_1093_, v_env_1092_, v_name_1091_);
    if v___x_1094_ == 0 {
        let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: u8 = 0;
        v___x_1095_ = l_Lake_leanExeAttr;
        v___x_1096_ = l_Lake_OrderedTagAttribute_hasTag(v___x_1095_, v_env_1092_, v_name_1091_);
        return v___x_1096_;
    } else {
        lean_dec_ref(v_env_1092_);
        return v___x_1094_;
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v_name_1097_: *mut LeanObject,
    mut v_env_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: u8 = 0;
    let mut v_r_1100_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v_name_1097_, v_env_1098_);
    lean_dec(v_name_1097_);
    v_r_1100_ = lean_box((v_res_1099_) as usize);
    return v_r_1100_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    v___x_1102_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
    return v___x_1103_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(
    mut v___f_1104_: *mut LeanObject,
    mut v_name_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_a_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1126_: u8 = 0;
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1109_ = lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1109_, 0, v_name_1105_);
                v___x_1110_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_1104_, v___f_1109_, v___y_1106_, v___y_1107_);
                if lean_obj_tag(v___x_1110_) == 0 {
                    v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
                    v_isSharedCheck_1122_ = (!lean_is_exclusive(v___x_1110_)) as u8;
                    if v_isSharedCheck_1122_ == 0 {
                        v___x_1113_ = v___x_1110_;
                        v_isShared_1114_ = v_isSharedCheck_1122_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1111_);
                        lean_dec(v___x_1110_);
                        v___x_1113_ = lean_box(0);
                        v_isShared_1114_ = v_isSharedCheck_1122_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1123_ = lean_ctor_get(v___x_1110_, 0);
                    v_isSharedCheck_1130_ = (!lean_is_exclusive(v___x_1110_)) as u8;
                    if v_isSharedCheck_1130_ == 0 {
                        v___x_1125_ = v___x_1110_;
                        v_isShared_1126_ = v_isSharedCheck_1130_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1123_);
                        lean_dec(v___x_1110_);
                        v___x_1125_ = lean_box(0);
                        v_isShared_1126_ = v_isSharedCheck_1130_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1115_ = (lean_unbox(v_a_1111_) as u8);
                lean_dec(v_a_1111_);
                if v___x_1115_ == 0 {
                    lean_del_object(v___x_1113_);
                    v___x_1116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_);
                    v___x_1117_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_1116_, v___y_1106_, v___y_1107_);
                    return v___x_1117_;
                } else {
                    v___x_1118_ = lean_box(0);
                    if v_isShared_1114_ == 0 {
                        lean_ctor_set(v___x_1113_, 0, v___x_1118_);
                        v___x_1120_ = v___x_1113_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
                        v___x_1120_ = v_reuseFailAlloc_1121_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1120_;
            }
            3 => {
                if v_isShared_1126_ == 0 {
                    v___x_1128_ = v___x_1125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
                    v___x_1128_ = v_reuseFailAlloc_1129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v___f_1131_: *mut LeanObject,
    mut v_name_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1136_: *mut LeanObject = core::ptr::null_mut();
    v_res_1136_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v___f_1131_, v_name_1132_, v___y_1133_, v___y_1134_);
    lean_dec(v___y_1134_);
    lean_dec_ref(v___y_1133_);
    return v_res_1136_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    v___f_1148_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1149_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1150_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1151_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1152_ =
        l_Lake_registerOrderedTagAttribute(v___x_1149_, v___x_1150_, v___f_1148_, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v_a_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
    return v_res_1154_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    v___f_1164_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1165_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1166_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1167_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1168_ =
        l_Lake_registerOrderedTagAttribute(v___x_1165_, v___x_1166_, v___f_1164_, v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2____boxed(
    mut v_a_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
    return v_res_1170_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___f_1180_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1181_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1182_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1183_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1184_ =
        l_Lake_registerOrderedTagAttribute(v___x_1181_, v___x_1182_, v___f_1180_, v___x_1183_);
    return v___x_1184_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2____boxed(
    mut v_a_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1186_: *mut LeanObject = core::ptr::null_mut();
    v_res_1186_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
    return v_res_1186_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    v___f_1196_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1197_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1198_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1199_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1200_ =
        l_Lake_registerOrderedTagAttribute(v___x_1197_, v___x_1198_, v___f_1196_, v___x_1199_);
    return v___x_1200_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2____boxed(
    mut v_a_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1202_: *mut LeanObject = core::ptr::null_mut();
    v_res_1202_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
    return v_res_1202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_AttributesCore(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_packageAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageDepAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_packageDepAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_postUpdateAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_postUpdateAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_scriptAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_scriptAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_defaultScriptAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_defaultScriptAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_leanLibAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_leanLibAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_leanExeAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_leanExeAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_externLibAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_externLibAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_inputFileAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_inputFileAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_inputDirAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_inputDirAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_targetAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_targetAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_defaultTargetAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_defaultTargetAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_testDriverAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_testDriverAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_lintDriverAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_lintDriverAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_moduleFacetAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_moduleFacetAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageFacetAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_packageFacetAttr);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_libraryFacetAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_libraryFacetAttr);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_AttributesCore(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_AttributesCore(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_AttributesCore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_AttributesCore(builtin);
}
