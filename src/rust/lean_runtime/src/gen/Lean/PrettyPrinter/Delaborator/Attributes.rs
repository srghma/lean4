// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Attributes
// Imports: Lean.Attributes
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent,
};
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [112, 112, 95, 117, 115, 105, 110, 103, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject,9594967107267031765 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanStringObject<65> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 60, m_data: [109, 97, 114, 107, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 116, 111, 32, 98, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 226, 159, 168, 97, 44, 98, 44, 99, 226, 159, 169, 96, 32, 110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [112, 112, 85, 115, 105, 110, 103, 65, 110, 111, 110, 121, 109, 111, 117, 115, 67, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject,3637194416493291231 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0_value: LeanStringObject<100> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 95, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 116, 111, 32, 98, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 97, 110, 111, 110, 121, 109, 111, 117, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 40, 96, 226, 159, 168, 97, 44, 32, 98, 44, 32, 99, 226, 159, 169, 96, 41, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 117 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 117 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 112, 95, 110, 111, 100, 111, 116, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject,9396143965797308935 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value: LeanStringObject<65> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [109, 97, 114, 107, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 102, 105, 101, 108, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 112, 78, 111, 68, 111, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject,14580985132438765898 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0_value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 102, 105, 101, 108, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut LeanObject,((( 99 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 99 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 30 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 30 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(
    mut v_x_142_: *mut LeanObject,
    mut v___y_143_: *mut LeanObject,
    mut v___y_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = lean_box(0);
    v___x_147_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_147_, 0, v___x_146_);
    return v___x_147_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(
    mut v_x_148_: *mut LeanObject,
    mut v___y_149_: *mut LeanObject,
    mut v___y_150_: *mut LeanObject,
    mut v___y_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_152_: *mut LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_(v_x_148_, v___y_149_, v___y_150_);
    lean_dec(v___y_150_);
    lean_dec_ref(v___y_149_);
    lean_dec(v_x_148_);
    return v_res_152_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: u8 = 0;
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___f_164_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_165_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_166_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_167_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_168_ = 0;
    v___x_169_ = lean_box(2);
    v___x_170_ = l_Lean_registerTagAttribute(
        v___x_165_, v___x_166_, v___f_164_, v___x_167_, v___x_168_, v___x_169_,
    );
    return v___x_170_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2____boxed(
    mut v_a_171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_172_: *mut LeanObject = core::ptr::null_mut();
    v_res_172_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_();
    return v_res_172_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    v___x_175_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_176_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___closed__0;
    v___x_177_ = l_Lean_addBuiltinDocString(v___x_175_, v___x_176_);
    return v___x_177_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1___boxed(
    mut v_a_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_179_: *mut LeanObject = core::ptr::null_mut();
    v_res_179_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1();
    return v_res_179_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    v___x_206_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_207_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___closed__6;
    v___x_208_ = l_Lean_addBuiltinDeclarationRanges(v___x_206_, v___x_207_);
    return v___x_208_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3___boxed(
    mut v_a_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3();
    return v_res_210_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: u8 = 0;
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    v___f_220_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_;
    v___x_221_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_;
    v___x_222_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_;
    v___x_223_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_;
    v___x_224_ = 0;
    v___x_225_ = lean_box(2);
    v___x_226_ = l_Lean_registerTagAttribute(
        v___x_221_, v___x_222_, v___f_220_, v___x_223_, v___x_224_, v___x_225_,
    );
    return v___x_226_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2____boxed(
    mut v_a_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_228_: *mut LeanObject = core::ptr::null_mut();
    v_res_228_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_();
    return v_res_228_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    v___x_231_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_;
    v___x_232_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___closed__0;
    v___x_233_ = l_Lean_addBuiltinDocString(v___x_231_, v___x_232_);
    return v___x_233_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1___boxed(
    mut v_a_234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_235_: *mut LeanObject = core::ptr::null_mut();
    v_res_235_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1();
    return v_res_235_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v___x_262_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_;
    v___x_263_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___closed__6;
    v___x_264_ = l_Lean_addBuiltinDeclarationRanges(v___x_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3___boxed(
    mut v_a_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_266_ = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3();
    return v_res_266_;
}
pub unsafe fn l_Lean_hasPPUsingAnonymousConstructorAttribute(
    mut v_env_267_: *mut LeanObject,
    mut v_declName_268_: *mut LeanObject,
) -> u8 {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: u8 = 0;
    v___x_269_ = l_Lean_ppUsingAnonymousConstructorAttr;
    v___x_270_ = l_Lean_TagAttribute_hasTag(v___x_269_, v_env_267_, v_declName_268_);
    return v___x_270_;
}
pub unsafe fn l_Lean_hasPPUsingAnonymousConstructorAttribute___boxed(
    mut v_env_271_: *mut LeanObject,
    mut v_declName_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_273_: u8 = 0;
    let mut v_r_274_: *mut LeanObject = core::ptr::null_mut();
    v_res_273_ = l_Lean_hasPPUsingAnonymousConstructorAttribute(v_env_271_, v_declName_272_);
    v_r_274_ = lean_box((v_res_273_) as usize);
    return v_r_274_;
}
pub unsafe fn l_Lean_hasPPNoDotAttribute(
    mut v_env_275_: *mut LeanObject,
    mut v_declName_276_: *mut LeanObject,
) -> u8 {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: u8 = 0;
    v___x_277_ = l_Lean_ppNoDotAttr;
    v___x_278_ = l_Lean_TagAttribute_hasTag(v___x_277_, v_env_275_, v_declName_276_);
    return v___x_278_;
}
pub unsafe fn l_Lean_hasPPNoDotAttribute___boxed(
    mut v_env_279_: *mut LeanObject,
    mut v_declName_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Lean_hasPPNoDotAttribute(v_env_279_, v_declName_280_);
    v_r_282_ = lean_box((v_res_281_) as usize);
    return v_r_282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_4229509627____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ppUsingAnonymousConstructorAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_ppUsingAnonymousConstructorAttr);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppUsingAnonymousConstructorAttr___regBuiltin_Lean_ppUsingAnonymousConstructorAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Attributes_2550701167____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ppNoDotAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_ppNoDotAttr);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Attributes_0__Lean_ppNoDotAttr___regBuiltin_Lean_ppNoDotAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_Attributes(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
}
