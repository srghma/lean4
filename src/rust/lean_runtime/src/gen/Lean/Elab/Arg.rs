// Lean compiler output
// Module: Lean.Elab.Arg
// Imports: Lean.Elab.Term
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId,
    l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_pop, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Lean_Elab_Term_instInhabitedArg_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedArg_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_instToStringArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instToStringArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Term_instToStringArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instToStringArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_instToMessageDataArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instToMessageDataArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Term_instToMessageDataArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToMessageDataArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instToMessageDataArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToMessageDataArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedNamedArg_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedNamedArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2_value: LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_instToStringNamedArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instToStringNamedArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Term_instToStringNamedArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringNamedArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instToStringNamedArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToStringNamedArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instToMessageDataNamedArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_addNamedArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [65, 114, 103, 117, 109, 101, 110, 116, 32, 96, 0],
    };
static mut l_Lean_Elab_Term_addNamedArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_addNamedArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_addNamedArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_addNamedArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_addNamedArg___closed__2_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            96, 32, 119, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Elab_Term_addNamedArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_addNamedArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_addNamedArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_addNamedArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value) as *mut LeanObject,13594530736035158498 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value) as *mut LeanObject,15691513163239863397 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 46, 46, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_expandArgs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Term_expandArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandArgs___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandArgs___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandArgs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_expandArgs___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_expandArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandArgs___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Term_Arg_ctorIdx(mut v_x_493_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_493_) == 0 {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        v___x_494_ = lean_unsigned_to_nat(0);
        return v___x_494_;
    } else {
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        v___x_495_ = lean_unsigned_to_nat(1);
        return v___x_495_;
    }
}
pub unsafe fn l_Lean_Elab_Term_Arg_ctorIdx___boxed(
    mut v_x_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_497_: *mut LeanObject = core::ptr::null_mut();
    v_res_497_ = l_Lean_Elab_Term_Arg_ctorIdx(v_x_496_);
    lean_dec_ref(v_x_496_);
    return v_res_497_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_ctorElim___redArg(
    mut v_t_498_: *mut LeanObject,
    mut v_k_499_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_498_) == 0 {
        let mut v_val_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
        v_val_500_ = lean_ctor_get(v_t_498_, 0);
        lean_inc(v_val_500_);
        lean_dec_ref_known(v_t_498_, 1);
        v___x_501_ = lean_apply_1(v_k_499_, v_val_500_);
        return v___x_501_;
    } else {
        let mut v_val_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        v_val_502_ = lean_ctor_get(v_t_498_, 0);
        lean_inc_ref(v_val_502_);
        lean_dec_ref_known(v_t_498_, 1);
        v___x_503_ = lean_apply_1(v_k_499_, v_val_502_);
        return v___x_503_;
    }
}
pub unsafe fn l_Lean_Elab_Term_Arg_ctorElim(
    mut v_motive_504_: *mut LeanObject,
    mut v_ctorIdx_505_: *mut LeanObject,
    mut v_t_506_: *mut LeanObject,
    mut v_h_507_: *mut LeanObject,
    mut v_k_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_506_, v_k_508_);
    return v___x_509_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_ctorElim___boxed(
    mut v_motive_510_: *mut LeanObject,
    mut v_ctorIdx_511_: *mut LeanObject,
    mut v_t_512_: *mut LeanObject,
    mut v_h_513_: *mut LeanObject,
    mut v_k_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_515_: *mut LeanObject = core::ptr::null_mut();
    v_res_515_ =
        l_Lean_Elab_Term_Arg_ctorElim(v_motive_510_, v_ctorIdx_511_, v_t_512_, v_h_513_, v_k_514_);
    lean_dec(v_ctorIdx_511_);
    return v_res_515_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_stx_elim___redArg(
    mut v_t_516_: *mut LeanObject,
    mut v_stx_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_516_, v_stx_517_);
    return v___x_518_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_stx_elim(
    mut v_motive_519_: *mut LeanObject,
    mut v_t_520_: *mut LeanObject,
    mut v_h_521_: *mut LeanObject,
    mut v_stx_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    v___x_523_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_520_, v_stx_522_);
    return v___x_523_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_expr_elim___redArg(
    mut v_t_524_: *mut LeanObject,
    mut v_expr_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_524_, v_expr_525_);
    return v___x_526_;
}
pub unsafe fn l_Lean_Elab_Term_Arg_expr_elim(
    mut v_motive_527_: *mut LeanObject,
    mut v_t_528_: *mut LeanObject,
    mut v_h_529_: *mut LeanObject,
    mut v_expr_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___x_531_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_528_, v_expr_530_);
    return v___x_531_;
}
pub unsafe fn l_Lean_Elab_Term_instToStringArg___lam__0(
    mut v_x_536_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_536_) == 0 {
        let mut v_val_537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_539_: u8 = 0;
        let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
        v_val_537_ = lean_ctor_get(v_x_536_, 0);
        lean_inc(v_val_537_);
        lean_dec_ref_known(v_x_536_, 1);
        v___x_538_ = lean_box(0);
        v___x_539_ = 0;
        v___x_540_ = l_Lean_Syntax_formatStx(v_val_537_, v___x_538_, v___x_539_);
        v___x_541_ = l_Std_Format_defWidth;
        v___x_542_ = lean_unsigned_to_nat(0);
        v___x_543_ = l_Std_Format_pretty(v___x_540_, v___x_541_, v___x_542_, v___x_542_);
        return v___x_543_;
    } else {
        let mut v_val_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        v_val_544_ = lean_ctor_get(v_x_536_, 0);
        lean_inc_ref(v_val_544_);
        lean_dec_ref_known(v_x_536_, 1);
        v___x_545_ = lean_expr_dbg_to_string(v_val_544_);
        lean_dec_ref(v_val_544_);
        return v___x_545_;
    }
}
pub unsafe fn l_Lean_Elab_Term_instToMessageDataArg___lam__0(
    mut v_x_548_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_548_) == 0 {
        let mut v_val_549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
        v_val_549_ = lean_ctor_get(v_x_548_, 0);
        lean_inc(v_val_549_);
        lean_dec_ref_known(v_x_548_, 1);
        v___x_550_ = l_Lean_MessageData_ofSyntax(v_val_549_);
        return v___x_550_;
    } else {
        let mut v_val_551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
        v_val_551_ = lean_ctor_get(v_x_548_, 0);
        lean_inc_ref(v_val_551_);
        lean_dec_ref_known(v_x_548_, 1);
        v___x_552_ = l_Lean_MessageData_ofExpr(v_val_551_);
        return v___x_552_;
    }
}
pub unsafe fn l_Lean_Elab_Term_instToStringNamedArg___lam__0(
    mut v_s_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_566_ = lean_ctor_get(v_s_565_, 1);
                lean_inc(v_name_566_);
                v_val_567_ = lean_ctor_get(v_s_565_, 2);
                lean_inc_ref(v_val_567_);
                lean_dec_ref(v_s_565_);
                v___x_568_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0;
                v___x_569_ = 1;
                v___x_570_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_566_,
                    v___x_569_,
                );
                v___x_571_ = lean_string_append(v___x_568_, v___x_570_);
                lean_dec_ref(v___x_570_);
                v___x_572_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1;
                v___x_573_ = lean_string_append(v___x_571_, v___x_572_);
                if lean_obj_tag(v_val_567_) == 0 {
                    v_val_579_ = lean_ctor_get(v_val_567_, 0);
                    lean_inc(v_val_579_);
                    lean_dec_ref_known(v_val_567_, 1);
                    v___x_580_ = lean_box(0);
                    v___x_581_ = 0;
                    v___x_582_ = l_Lean_Syntax_formatStx(v_val_579_, v___x_580_, v___x_581_);
                    v___x_583_ = l_Std_Format_defWidth;
                    v___x_584_ = lean_unsigned_to_nat(0);
                    v___x_585_ =
                        l_Std_Format_pretty(v___x_582_, v___x_583_, v___x_584_, v___x_584_);
                    v___y_575_ = v___x_585_;
                    state = 1;
                    continue;
                } else {
                    v_val_586_ = lean_ctor_get(v_val_567_, 0);
                    lean_inc_ref(v_val_586_);
                    lean_dec_ref_known(v_val_567_, 1);
                    v___x_587_ = lean_expr_dbg_to_string(v_val_586_);
                    lean_dec_ref(v_val_586_);
                    v___y_575_ = v___x_587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_576_ = lean_string_append(v___x_573_, v___y_575_);
                lean_dec_ref(v___y_575_);
                v___x_577_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2;
                v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
                return v___x_578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    v___x_590_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0;
    v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
    return v___x_591_;
}
pub unsafe fn _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1;
    v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_594_ = l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2;
    v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
    return v___x_595_;
}
pub unsafe fn l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0(
    mut v_s_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_597_ = lean_ctor_get(v_s_596_, 1);
                lean_inc(v_name_597_);
                v_val_598_ = lean_ctor_get(v_s_596_, 2);
                lean_inc_ref(v_val_598_);
                lean_dec_ref(v_s_596_);
                v___x_599_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0,
                );
                v___x_600_ = l_Lean_MessageData_ofName(v_name_597_);
                v___x_601_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_601_, 0, v___x_599_);
                lean_ctor_set(v___x_601_, 1, v___x_600_);
                v___x_602_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1,
                );
                v___x_603_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_603_, 0, v___x_601_);
                lean_ctor_set(v___x_603_, 1, v___x_602_);
                if lean_obj_tag(v_val_598_) == 0 {
                    v_val_609_ = lean_ctor_get(v_val_598_, 0);
                    lean_inc(v_val_609_);
                    lean_dec_ref_known(v_val_598_, 1);
                    v___x_610_ = l_Lean_MessageData_ofSyntax(v_val_609_);
                    v___y_605_ = v___x_610_;
                    state = 1;
                    continue;
                } else {
                    v_val_611_ = lean_ctor_get(v_val_598_, 0);
                    lean_inc_ref(v_val_611_);
                    lean_dec_ref_known(v_val_598_, 1);
                    v___x_612_ = l_Lean_MessageData_ofExpr(v_val_611_);
                    v___y_605_ = v___x_612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_606_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_606_, 0, v___x_603_);
                lean_ctor_set(v___x_606_, 1, v___y_605_);
                v___x_607_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2,
                );
                v___x_608_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_608_, 0, v___x_606_);
                lean_ctor_set(v___x_608_, 1, v___x_607_);
                return v___x_608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(
    mut v_msgData_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
    mut v___y_617_: *mut LeanObject,
    mut v___y_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_st_ref_get(v___y_619_);
    v_env_622_ = lean_ctor_get(v___x_621_, 0);
    lean_inc_ref(v_env_622_);
    lean_dec(v___x_621_);
    v___x_623_ = lean_st_ref_get(v___y_617_);
    v_mctx_624_ = lean_ctor_get(v___x_623_, 0);
    lean_inc_ref(v_mctx_624_);
    lean_dec(v___x_623_);
    v_lctx_625_ = lean_ctor_get(v___y_616_, 2);
    v_options_626_ = lean_ctor_get(v___y_618_, 2);
    lean_inc_ref(v_options_626_);
    lean_inc_ref(v_lctx_625_);
    v___x_627_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_627_, 0, v_env_622_);
    lean_ctor_set(v___x_627_, 1, v_mctx_624_);
    lean_ctor_set(v___x_627_, 2, v_lctx_625_);
    lean_ctor_set(v___x_627_, 3, v_options_626_);
    v___x_628_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_628_, 0, v___x_627_);
    lean_ctor_set(v___x_628_, 1, v_msgData_615_);
    v___x_629_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_629_, 0, v___x_628_);
    return v___x_629_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_630_: *mut LeanObject,
    mut v___y_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_636_: *mut LeanObject = core::ptr::null_mut();
    v_res_636_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msgData_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
    lean_dec(v___y_634_);
    lean_dec_ref(v___y_633_);
    lean_dec(v___y_632_);
    lean_dec_ref(v___y_631_);
    return v_res_636_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(
    mut v_msg_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
    mut v___y_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_643_ = lean_ctor_get(v___y_640_, 5);
                v___x_644_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
                v_a_645_ = lean_ctor_get(v___x_644_, 0);
                v_isSharedCheck_653_ = (!lean_is_exclusive(v___x_644_)) as u8;
                if v_isSharedCheck_653_ == 0 {
                    v___x_647_ = v___x_644_;
                    v_isShared_648_ = v_isSharedCheck_653_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_645_);
                    lean_dec(v___x_644_);
                    v___x_647_ = lean_box(0);
                    v_isShared_648_ = v_isSharedCheck_653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_643_);
                v___x_649_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_649_, 0, v_ref_643_);
                lean_ctor_set(v___x_649_, 1, v_a_645_);
                if v_isShared_648_ == 0 {
                    lean_ctor_set_tag(v___x_647_, 1);
                    lean_ctor_set(v___x_647_, 0, v___x_649_);
                    v___x_651_ = v___x_647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
                    v___x_651_ = v_reuseFailAlloc_652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg___boxed(
    mut v_msg_654_: *mut LeanObject,
    mut v___y_655_: *mut LeanObject,
    mut v___y_656_: *mut LeanObject,
    mut v___y_657_: *mut LeanObject,
    mut v___y_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
    lean_dec(v___y_658_);
    lean_dec_ref(v___y_657_);
    lean_dec(v___y_656_);
    lean_dec_ref(v___y_655_);
    return v_res_660_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(
    mut v_ref_661_: *mut LeanObject,
    mut v_msg_662_: *mut LeanObject,
    mut v___y_663_: *mut LeanObject,
    mut v___y_664_: *mut LeanObject,
    mut v___y_665_: *mut LeanObject,
    mut v___y_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_680_: u8 = 0;
    let mut v_cancelTk_x3f_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_682_: u8 = 0;
    let mut v_inheritedTraceOptions_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_668_ = lean_ctor_get(v___y_665_, 0);
    v_fileMap_669_ = lean_ctor_get(v___y_665_, 1);
    v_options_670_ = lean_ctor_get(v___y_665_, 2);
    v_currRecDepth_671_ = lean_ctor_get(v___y_665_, 3);
    v_maxRecDepth_672_ = lean_ctor_get(v___y_665_, 4);
    v_ref_673_ = lean_ctor_get(v___y_665_, 5);
    v_currNamespace_674_ = lean_ctor_get(v___y_665_, 6);
    v_openDecls_675_ = lean_ctor_get(v___y_665_, 7);
    v_initHeartbeats_676_ = lean_ctor_get(v___y_665_, 8);
    v_maxHeartbeats_677_ = lean_ctor_get(v___y_665_, 9);
    v_quotContext_678_ = lean_ctor_get(v___y_665_, 10);
    v_currMacroScope_679_ = lean_ctor_get(v___y_665_, 11);
    v_diag_680_ = lean_ctor_get_uint8(
        v___y_665_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_681_ = lean_ctor_get(v___y_665_, 12);
    v_suppressElabErrors_682_ = lean_ctor_get_uint8(
        v___y_665_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_683_ = lean_ctor_get(v___y_665_, 13);
    v_ref_684_ = l_Lean_replaceRef(v_ref_661_, v_ref_673_);
    lean_inc_ref(v_inheritedTraceOptions_683_);
    lean_inc(v_cancelTk_x3f_681_);
    lean_inc(v_currMacroScope_679_);
    lean_inc(v_quotContext_678_);
    lean_inc(v_maxHeartbeats_677_);
    lean_inc(v_initHeartbeats_676_);
    lean_inc(v_openDecls_675_);
    lean_inc(v_currNamespace_674_);
    lean_inc(v_maxRecDepth_672_);
    lean_inc(v_currRecDepth_671_);
    lean_inc_ref(v_options_670_);
    lean_inc_ref(v_fileMap_669_);
    lean_inc_ref(v_fileName_668_);
    v___x_685_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_685_, 0, v_fileName_668_);
    lean_ctor_set(v___x_685_, 1, v_fileMap_669_);
    lean_ctor_set(v___x_685_, 2, v_options_670_);
    lean_ctor_set(v___x_685_, 3, v_currRecDepth_671_);
    lean_ctor_set(v___x_685_, 4, v_maxRecDepth_672_);
    lean_ctor_set(v___x_685_, 5, v_ref_684_);
    lean_ctor_set(v___x_685_, 6, v_currNamespace_674_);
    lean_ctor_set(v___x_685_, 7, v_openDecls_675_);
    lean_ctor_set(v___x_685_, 8, v_initHeartbeats_676_);
    lean_ctor_set(v___x_685_, 9, v_maxHeartbeats_677_);
    lean_ctor_set(v___x_685_, 10, v_quotContext_678_);
    lean_ctor_set(v___x_685_, 11, v_currMacroScope_679_);
    lean_ctor_set(v___x_685_, 12, v_cancelTk_x3f_681_);
    lean_ctor_set(v___x_685_, 13, v_inheritedTraceOptions_683_);
    lean_ctor_set_uint8(
        v___x_685_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_680_,
    );
    lean_ctor_set_uint8(
        v___x_685_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_682_,
    );
    v___x_686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_662_, v___y_663_, v___y_664_, v___x_685_, v___y_666_);
    lean_dec_ref_known(v___x_685_, 14);
    return v___x_686_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(
    mut v_ref_687_: *mut LeanObject,
    mut v_msg_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(
        v_ref_687_, v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_,
    );
    lean_dec(v___y_692_);
    lean_dec_ref(v___y_691_);
    lean_dec(v___y_690_);
    lean_dec_ref(v___y_689_);
    lean_dec(v_ref_687_);
    return v_res_694_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(
    mut v_namedArg_695_: *mut LeanObject,
    mut v_as_696_: *mut LeanObject,
    mut v_i_697_: usize,
    mut v_stop_698_: usize,
) -> u8 {
    let mut v___x_699_: u8 = 0;
    let mut v_name_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: usize = 0;
    let mut v___x_705_: usize = 0;
    let mut v___x_707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_699_ = lean_usize_dec_eq(v_i_697_, v_stop_698_);
                if v___x_699_ == 0 {
                    v_name_700_ = lean_ctor_get(v_namedArg_695_, 1);
                    v___x_701_ = lean_array_uget_borrowed(v_as_696_, v_i_697_);
                    v_name_702_ = lean_ctor_get(v___x_701_, 1);
                    v___x_703_ = lean_name_eq(v_name_700_, v_name_702_);
                    if v___x_703_ == 0 {
                        v___x_704_ = 1usize;
                        v___x_705_ = lean_usize_add(v_i_697_, v___x_704_);
                        v_i_697_ = v___x_705_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_703_;
                    }
                } else {
                    v___x_707_ = 0;
                    return v___x_707_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(
    mut v_namedArg_708_: *mut LeanObject,
    mut v_as_709_: *mut LeanObject,
    mut v_i_710_: *mut LeanObject,
    mut v_stop_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_712_: usize = 0;
    let mut v_stop_boxed_713_: usize = 0;
    let mut v_res_714_: u8 = 0;
    let mut v_r_715_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_712_ = lean_unbox_usize(v_i_710_);
    lean_dec(v_i_710_);
    v_stop_boxed_713_ = lean_unbox_usize(v_stop_711_);
    lean_dec(v_stop_711_);
    v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_708_, v_as_709_, v_i_boxed_712_, v_stop_boxed_713_);
    lean_dec_ref(v_as_709_);
    lean_dec_ref(v_namedArg_708_);
    v_r_715_ = lean_box((v_res_714_) as usize);
    return v_r_715_;
}
pub unsafe fn _init_l_Lean_Elab_Term_addNamedArg___closed__1() -> *mut LeanObject {
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    v___x_717_ = l_Lean_Elab_Term_addNamedArg___closed__0;
    v___x_718_ = l_Lean_stringToMessageData(v___x_717_);
    return v___x_718_;
}
pub unsafe fn _init_l_Lean_Elab_Term_addNamedArg___closed__3() -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_Elab_Term_addNamedArg___closed__2;
    v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
    return v___x_721_;
}
pub unsafe fn l_Lean_Elab_Term_addNamedArg(
    mut v_namedArgs_722_: *mut LeanObject,
    mut v_namedArg_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: usize = 0;
    let mut v___x_736_: usize = 0;
    let mut v___x_737_: u8 = 0;
    let mut v_ref_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_732_ = lean_unsigned_to_nat(0);
                v___x_733_ = lean_array_get_size(v_namedArgs_722_);
                v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
                if v___x_734_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v___x_734_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_735_ = 0usize;
                        v___x_736_ = lean_usize_of_nat(v___x_733_);
                        v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_723_, v_namedArgs_722_, v___x_735_, v___x_736_);
                        if v___x_737_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_namedArgs_722_);
                            v_ref_738_ = lean_ctor_get(v_namedArg_723_, 0);
                            lean_inc(v_ref_738_);
                            v_name_739_ = lean_ctor_get(v_namedArg_723_, 1);
                            lean_inc(v_name_739_);
                            lean_dec_ref(v_namedArg_723_);
                            v___x_740_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Elab_Term_addNamedArg___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_addNamedArg___closed__1_once
                                ),
                                _init_l_Lean_Elab_Term_addNamedArg___closed__1,
                            );
                            v___x_741_ = l_Lean_MessageData_ofName(v_name_739_);
                            v___x_742_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_742_, 0, v___x_740_);
                            lean_ctor_set(v___x_742_, 1, v___x_741_);
                            v___x_743_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Elab_Term_addNamedArg___closed__3),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_addNamedArg___closed__3_once
                                ),
                                _init_l_Lean_Elab_Term_addNamedArg___closed__3,
                            );
                            v___x_744_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_744_, 0, v___x_742_);
                            lean_ctor_set(v___x_744_, 1, v___x_743_);
                            v___x_745_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_738_, v___x_744_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                            lean_dec(v_ref_738_);
                            v_a_746_ = lean_ctor_get(v___x_745_, 0);
                            v_isSharedCheck_753_ = (!lean_is_exclusive(v___x_745_)) as u8;
                            if v_isSharedCheck_753_ == 0 {
                                v___x_748_ = v___x_745_;
                                v_isShared_749_ = v_isSharedCheck_753_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_746_);
                                lean_dec(v___x_745_);
                                v___x_748_ = lean_box(0);
                                v_isShared_749_ = v_isSharedCheck_753_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_730_ = lean_array_push(v_namedArgs_722_, v_namedArg_723_);
                v___x_731_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_731_, 0, v___x_730_);
                return v___x_731_;
            }
            2 => {
                if v_isShared_749_ == 0 {
                    v___x_751_ = v___x_748_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
                    v___x_751_ = v_reuseFailAlloc_752_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_addNamedArg___boxed(
    mut v_namedArgs_754_: *mut LeanObject,
    mut v_namedArg_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_761_ = l_Lean_Elab_Term_addNamedArg(
        v_namedArgs_754_,
        v_namedArg_755_,
        v_a_756_,
        v_a_757_,
        v_a_758_,
        v_a_759_,
    );
    lean_dec(v_a_759_);
    lean_dec_ref(v_a_758_);
    lean_dec(v_a_757_);
    lean_dec_ref(v_a_756_);
    return v_res_761_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(
    mut v_00_u03b1_762_: *mut LeanObject,
    mut v_ref_763_: *mut LeanObject,
    mut v_msg_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(
        v_ref_763_, v_msg_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_,
    );
    return v___x_770_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(
    mut v_00_u03b1_771_: *mut LeanObject,
    mut v_ref_772_: *mut LeanObject,
    mut v_msg_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_779_: *mut LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(
        v_00_u03b1_771_,
        v_ref_772_,
        v_msg_773_,
        v___y_774_,
        v___y_775_,
        v___y_776_,
        v___y_777_,
    );
    lean_dec(v___y_777_);
    lean_dec_ref(v___y_776_);
    lean_dec(v___y_775_);
    lean_dec_ref(v___y_774_);
    lean_dec(v_ref_772_);
    return v_res_779_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(
    mut v_00_u03b1_780_: *mut LeanObject,
    mut v_msg_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
    return v___x_787_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(
    mut v_00_u03b1_788_: *mut LeanObject,
    mut v_msg_789_: *mut LeanObject,
    mut v___y_790_: *mut LeanObject,
    mut v___y_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_795_: *mut LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(v_00_u03b1_788_, v_msg_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
    lean_dec(v___y_793_);
    lean_dec_ref(v___y_792_);
    lean_dec(v___y_791_);
    lean_dec_ref(v___y_790_);
    return v_res_795_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8()
-> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7;
    v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
    return v___x_813_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(
    mut v_as_814_: *mut LeanObject,
    mut v_i_815_: usize,
    mut v_stop_816_: usize,
    mut v_b_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
    mut v___y_820_: *mut LeanObject,
    mut v___y_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: usize = 0;
    let mut v___x_826_: usize = 0;
    let mut v___x_828_: u8 = 0;
    let mut v_fst_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_833_: u8 = 0;
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_865_: u8 = 0;
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_828_ = lean_usize_dec_eq(v_i_815_, v_stop_816_);
                if v___x_828_ == 0 {
                    v_fst_829_ = lean_ctor_get(v_b_817_, 0);
                    v_snd_830_ = lean_ctor_get(v_b_817_, 1);
                    v_isSharedCheck_870_ = (!lean_is_exclusive(v_b_817_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_832_ = v_b_817_;
                        v_isShared_833_ = v_isSharedCheck_870_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_830_);
                        lean_inc(v_fst_829_);
                        lean_dec(v_b_817_);
                        v___x_832_ = lean_box(0);
                        v_isShared_833_ = v_isSharedCheck_870_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_871_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_871_, 0, v_b_817_);
                    return v___x_871_;
                }
            }
            1 => {
                v___x_825_ = 1usize;
                v___x_826_ = lean_usize_add(v_i_815_, v___x_825_);
                v_i_815_ = v___x_826_;
                v_b_817_ = v_a_824_;
                state = 0;
                continue;
            }
            2 => {
                v___x_834_ = lean_array_uget_borrowed(v_as_814_, v_i_815_);
                lean_inc(v___x_834_);
                v___x_835_ = l_Lean_Syntax_getKind(v___x_834_);
                v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4;
                v___x_837_ = lean_name_eq(v___x_835_, v___x_836_);
                if v___x_837_ == 0 {
                    v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6;
                    v___x_839_ = lean_name_eq(v___x_835_, v___x_838_);
                    lean_dec(v___x_835_);
                    if v___x_839_ == 0 {
                        lean_inc(v___x_834_);
                        v___x_840_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_840_, 0, v___x_834_);
                        v___x_841_ = lean_array_push(v_snd_830_, v___x_840_);
                        if v_isShared_833_ == 0 {
                            lean_ctor_set(v___x_832_, 1, v___x_841_);
                            v___x_843_ = v___x_832_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_829_);
                            lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
                            v___x_843_ = v_reuseFailAlloc_844_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_832_);
                        lean_dec(v_snd_830_);
                        lean_dec(v_fst_829_);
                        v___x_845_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8);
                        v___x_846_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v___x_834_, v___x_845_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
                        if lean_obj_tag(v___x_846_) == 0 {
                            v_a_847_ = lean_ctor_get(v___x_846_, 0);
                            lean_inc(v_a_847_);
                            lean_dec_ref_known(v___x_846_, 1);
                            v_a_824_ = v_a_847_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_846_;
                        }
                    }
                } else {
                    lean_dec(v___x_835_);
                    v___x_848_ = lean_unsigned_to_nat(1);
                    v___x_849_ = l_Lean_Syntax_getArg(v___x_834_, v___x_848_);
                    v___x_850_ = l_Lean_Syntax_getId(v___x_849_);
                    lean_dec(v___x_849_);
                    v_name_851_ = lean_erase_macro_scopes(v___x_850_);
                    v___x_852_ = lean_unsigned_to_nat(3);
                    v_val_853_ = l_Lean_Syntax_getArg(v___x_834_, v___x_852_);
                    v___x_854_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_854_, 0, v_val_853_);
                    v___x_855_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_834_);
                    v___x_856_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_856_, 0, v___x_834_);
                    lean_ctor_set(v___x_856_, 1, v_name_851_);
                    lean_ctor_set(v___x_856_, 2, v___x_854_);
                    lean_ctor_set(v___x_856_, 3, v___x_855_);
                    v___x_857_ = l_Lean_Elab_Term_addNamedArg(
                        v_fst_829_, v___x_856_, v___y_818_, v___y_819_, v___y_820_, v___y_821_,
                    );
                    if lean_obj_tag(v___x_857_) == 0 {
                        v_a_858_ = lean_ctor_get(v___x_857_, 0);
                        lean_inc(v_a_858_);
                        lean_dec_ref_known(v___x_857_, 1);
                        if v_isShared_833_ == 0 {
                            lean_ctor_set(v___x_832_, 0, v_a_858_);
                            v___x_860_ = v___x_832_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_858_);
                            lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_830_);
                            v___x_860_ = v_reuseFailAlloc_861_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_832_);
                        lean_dec(v_snd_830_);
                        v_a_862_ = lean_ctor_get(v___x_857_, 0);
                        v_isSharedCheck_869_ = (!lean_is_exclusive(v___x_857_)) as u8;
                        if v_isSharedCheck_869_ == 0 {
                            v___x_864_ = v___x_857_;
                            v_isShared_865_ = v_isSharedCheck_869_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_862_);
                            lean_dec(v___x_857_);
                            v___x_864_ = lean_box(0);
                            v_isShared_865_ = v_isSharedCheck_869_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_824_ = v___x_843_;
                state = 1;
                continue;
            }
            4 => {
                v_a_824_ = v___x_860_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_865_ == 0 {
                    v___x_867_ = v___x_864_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
                    v___x_867_ = v_reuseFailAlloc_868_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(
    mut v_as_872_: *mut LeanObject,
    mut v_i_873_: *mut LeanObject,
    mut v_stop_874_: *mut LeanObject,
    mut v_b_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
    mut v___y_879_: *mut LeanObject,
    mut v___y_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_881_: usize = 0;
    let mut v_stop_boxed_882_: usize = 0;
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_881_ = lean_unbox_usize(v_i_873_);
    lean_dec(v_i_873_);
    v_stop_boxed_882_ = lean_unbox_usize(v_stop_874_);
    lean_dec(v_stop_874_);
    v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_872_, v_i_boxed_881_, v_stop_boxed_882_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
    lean_dec(v___y_879_);
    lean_dec_ref(v___y_878_);
    lean_dec(v___y_877_);
    lean_dec_ref(v___y_876_);
    lean_dec_ref(v_as_872_);
    return v_res_883_;
}
pub unsafe fn l_Lean_Elab_Term_expandArgs(
    mut v_args_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
    mut v_a_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_a_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_895_: u8 = 0;
    let mut v_fst_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_903_: u8 = 0;
    let mut v___y_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_911_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v_fst_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_918_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: usize = 0;
    let mut v___x_929_: usize = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_931_ = lean_array_get_size(v_args_888_);
                v___x_932_ = lean_unsigned_to_nat(0);
                v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
                if v___x_933_ == 0 {
                    v___x_934_ = lean_box(0);
                    v___x_935_ = lean_unsigned_to_nat(1);
                    v___x_936_ = lean_nat_sub(v___x_931_, v___x_935_);
                    v___x_937_ = lean_array_get_borrowed(v___x_934_, v_args_888_, v___x_936_);
                    lean_dec(v___x_936_);
                    v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6;
                    lean_inc(v___x_937_);
                    v___x_939_ = l_Lean_Syntax_isOfKind(v___x_937_, v___x_938_);
                    if v___x_939_ == 0 {
                        v_fst_917_ = v_args_888_;
                        v_snd_918_ = v___x_939_;
                        state = 5;
                        continue;
                    } else {
                        v___x_940_ = lean_array_pop(v_args_888_);
                        v_fst_917_ = v___x_940_;
                        v_snd_918_ = v___x_939_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_941_ = 0;
                    v_fst_917_ = v_args_888_;
                    v_snd_918_ = v___x_941_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_898_ = lean_box((v___y_895_) as usize);
                v___x_899_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_899_, 0, v_snd_897_);
                lean_ctor_set(v___x_899_, 1, v___x_898_);
                v___x_900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_900_, 0, v_fst_896_);
                lean_ctor_set(v___x_900_, 1, v___x_899_);
                v___x_901_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_901_, 0, v___x_900_);
                return v___x_901_;
            }
            2 => {
                if lean_obj_tag(v___y_904_) == 0 {
                    v_a_905_ = lean_ctor_get(v___y_904_, 0);
                    lean_inc(v_a_905_);
                    lean_dec_ref_known(v___y_904_, 1);
                    v_fst_906_ = lean_ctor_get(v_a_905_, 0);
                    lean_inc(v_fst_906_);
                    v_snd_907_ = lean_ctor_get(v_a_905_, 1);
                    lean_inc(v_snd_907_);
                    lean_dec(v_a_905_);
                    v___y_895_ = v___y_903_;
                    v_fst_896_ = v_fst_906_;
                    v_snd_897_ = v_snd_907_;
                    state = 1;
                    continue;
                } else {
                    v_a_908_ = lean_ctor_get(v___y_904_, 0);
                    v_isSharedCheck_915_ = (!lean_is_exclusive(v___y_904_)) as u8;
                    if v_isSharedCheck_915_ == 0 {
                        v___x_910_ = v___y_904_;
                        v_isShared_911_ = v_isSharedCheck_915_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_908_);
                        lean_dec(v___y_904_);
                        v___x_910_ = lean_box(0);
                        v_isShared_911_ = v_isSharedCheck_915_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_911_ == 0 {
                    v___x_913_ = v___x_910_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
                    v___x_913_ = v_reuseFailAlloc_914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_913_;
            }
            5 => {
                v___x_919_ = lean_unsigned_to_nat(0);
                v___x_920_ = l_Lean_Elab_Term_expandArgs___closed__0;
                v___x_921_ = lean_array_get_size(v_fst_917_);
                v___x_922_ = lean_nat_dec_lt(v___x_919_, v___x_921_);
                if v___x_922_ == 0 {
                    lean_dec_ref(v_fst_917_);
                    v___y_895_ = v_snd_918_;
                    v_fst_896_ = v___x_920_;
                    v_snd_897_ = v___x_920_;
                    state = 1;
                    continue;
                } else {
                    v___x_923_ = l_Lean_Elab_Term_expandArgs___closed__1;
                    v___x_924_ = lean_nat_dec_le(v___x_921_, v___x_921_);
                    if v___x_924_ == 0 {
                        if v___x_922_ == 0 {
                            lean_dec_ref(v_fst_917_);
                            v___y_895_ = v_snd_918_;
                            v_fst_896_ = v___x_920_;
                            v_snd_897_ = v___x_920_;
                            state = 1;
                            continue;
                        } else {
                            v___x_925_ = 0usize;
                            v___x_926_ = lean_usize_of_nat(v___x_921_);
                            v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_917_, v___x_925_, v___x_926_, v___x_923_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
                            lean_dec_ref(v_fst_917_);
                            v___y_903_ = v_snd_918_;
                            v___y_904_ = v___x_927_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_928_ = 0usize;
                        v___x_929_ = lean_usize_of_nat(v___x_921_);
                        v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_917_, v___x_928_, v___x_929_, v___x_923_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
                        lean_dec_ref(v_fst_917_);
                        v___y_903_ = v_snd_918_;
                        v___y_904_ = v___x_930_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandArgs___boxed(
    mut v_args_942_: *mut LeanObject,
    mut v_a_943_: *mut LeanObject,
    mut v_a_944_: *mut LeanObject,
    mut v_a_945_: *mut LeanObject,
    mut v_a_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_948_: *mut LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Elab_Term_expandArgs(v_args_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
    lean_dec(v_a_946_);
    lean_dec_ref(v_a_945_);
    lean_dec(v_a_944_);
    lean_dec_ref(v_a_943_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Elab_Term_expandApp(
    mut v_stx_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_962_: u8 = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut v_a_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_973_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_955_ = lean_unsigned_to_nat(1);
                v___x_956_ = l_Lean_Syntax_getArg(v_stx_949_, v___x_955_);
                v___x_957_ = l_Lean_Syntax_getArgs(v___x_956_);
                lean_dec(v___x_956_);
                v___x_958_ =
                    l_Lean_Elab_Term_expandArgs(v___x_957_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
                if lean_obj_tag(v___x_958_) == 0 {
                    v_a_959_ = lean_ctor_get(v___x_958_, 0);
                    v_isSharedCheck_969_ = (!lean_is_exclusive(v___x_958_)) as u8;
                    if v_isSharedCheck_969_ == 0 {
                        v___x_961_ = v___x_958_;
                        v_isShared_962_ = v_isSharedCheck_969_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_959_);
                        lean_dec(v___x_958_);
                        v___x_961_ = lean_box(0);
                        v_isShared_962_ = v_isSharedCheck_969_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_970_ = lean_ctor_get(v___x_958_, 0);
                    v_isSharedCheck_977_ = (!lean_is_exclusive(v___x_958_)) as u8;
                    if v_isSharedCheck_977_ == 0 {
                        v___x_972_ = v___x_958_;
                        v_isShared_973_ = v_isSharedCheck_977_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_970_);
                        lean_dec(v___x_958_);
                        v___x_972_ = lean_box(0);
                        v_isShared_973_ = v_isSharedCheck_977_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_963_ = lean_unsigned_to_nat(0);
                v___x_964_ = l_Lean_Syntax_getArg(v_stx_949_, v___x_963_);
                v___x_965_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_965_, 0, v___x_964_);
                lean_ctor_set(v___x_965_, 1, v_a_959_);
                if v_isShared_962_ == 0 {
                    lean_ctor_set(v___x_961_, 0, v___x_965_);
                    v___x_967_ = v___x_961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
                    v___x_967_ = v_reuseFailAlloc_968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_967_;
            }
            3 => {
                if v_isShared_973_ == 0 {
                    v___x_975_ = v___x_972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
                    v___x_975_ = v_reuseFailAlloc_976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandApp___boxed(
    mut v_stx_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_984_: *mut LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_Elab_Term_expandApp(v_stx_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
    lean_dec(v_a_982_);
    lean_dec_ref(v_a_981_);
    lean_dec(v_a_980_);
    lean_dec_ref(v_a_979_);
    lean_dec(v_stx_978_);
    return v_res_984_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Arg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Arg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Arg(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Arg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Arg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Arg(builtin);
}
