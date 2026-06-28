// Lean compiler output
// Module: Lean.Meta.Match.MatcherInfo
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr5, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg, l_Lean_TagDeclarationExtension_isTagged,
    l_Lean_TagDeclarationExtension_tag, l_Lean_mkTagDeclarationExtension,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_setExporting,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_string_utf8_byte_size, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lean_Meta_Match_instInhabitedDiscrInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedDiscrInfo: *mut LeanObject = core::ptr::null_mut();
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value: LeanStringObject<
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [104, 78, 97, 109, 101, 63, 0],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value: LeanStringObject<
    5,
> = LeanStringObject {
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
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value: LeanStringObject<
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_instReprDiscrInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instReprDiscrInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedOverlaps_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedOverlaps: *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value) as *mut LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value) as *mut LeanObject;
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value) as *mut LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value) as *mut LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 111, 102, 76, 105, 115, 116, 32, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value) as *mut LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value: LeanStringObject<4> =
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
        m_data: [109, 97, 112, 0],
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_instReprOverlaps_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_instReprOverlaps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instReprOverlaps: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Match_Overlaps_overlapping___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltParamInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltParamInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 117, 109, 70, 105, 101, 108, 100, 115, 0],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value:
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
    m_data: [110, 117, 109, 79, 118, 101, 114, 108, 97, 112, 115, 0],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value:
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
    m_data: [104, 97, 115, 85, 110, 105, 116, 84, 104, 117, 110, 107, 0],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_instReprAltParamInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instReprAltParamInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_instBEqAltParamInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instBEqAltParamInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatcherInfo: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 117, 109, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 117, 109, 68, 105, 115, 99, 114, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 108, 116, 73, 110, 102, 111, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [117, 69, 108, 105, 109, 80, 111, 115, 63, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value:
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
    m_data: [100, 105, 115, 99, 114, 73, 110, 102, 111, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value:
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
    m_data: [111, 118, 101, 114, 108, 97, 112, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_instReprMatcherInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instReprMatcherInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_Extension_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,5431323822491600447 as *mut LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,3008809457587767149 as *mut LeanObject] };
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,18229679040985057098 as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Match_Extension_State_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 97, 116, 99, 104, 95, 0],
    };
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 97, 116, 99, 104, 101, 114, 76, 105, 107, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut LeanObject,1902021009172655898 as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default() -> *mut LeanObject {
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2376_ = lean_box(0);
    return v___x_2376_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedDiscrInfo() -> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = lean_box(0);
    return v___x_2377_;
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(
    mut v_x_2384_: *mut LeanObject,
    mut v_x_2385_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2384_) == 0 {
        let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
        v___x_2386_ =
            l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1;
        return v___x_2386_;
    } else {
        let mut v_val_2387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
        v_val_2387_ = lean_ctor_get(v_x_2384_, 0);
        lean_inc(v_val_2387_);
        lean_dec_ref_known(v_x_2384_, 1);
        v___x_2388_ =
            l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3;
        v___x_2389_ = lean_unsigned_to_nat(1024);
        v___x_2390_ = l_Lean_Name_reprPrec(v_val_2387_, v___x_2389_);
        v___x_2391_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2391_, 0, v___x_2388_);
        lean_ctor_set(v___x_2391_, 1, v___x_2390_);
        v___x_2392_ = l_Repr_addAppParen(v___x_2391_, v_x_2385_);
        return v___x_2392_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(
    mut v_x_2393_: *mut LeanObject,
    mut v_x_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ =
        l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_2393_, v_x_2394_);
    lean_dec(v_x_2394_);
    return v_res_2395_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(
    mut v_a_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = lean_nat_to_int(v_a_2396_);
    return v___x_2397_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = lean_unsigned_to_nat(10);
    v___x_2412_ = lean_nat_to_int(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0;
    v___x_2415_ = lean_string_length(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    v___x_2416_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9,
    );
    v___x_2417_ = lean_nat_to_int(v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(
    mut v_x_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6;
    v___x_2424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7,
    );
    v___x_2425_ = lean_unsigned_to_nat(0);
    v___x_2426_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(
        v_x_2422_,
        v___x_2425_,
    );
    v___x_2427_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2427_, 0, v___x_2424_);
    lean_ctor_set(v___x_2427_, 1, v___x_2426_);
    v___x_2428_ = 0;
    v___x_2429_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2429_, 0, v___x_2427_);
    lean_ctor_set_uint8(
        v___x_2429_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2428_,
    );
    v___x_2430_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2430_, 0, v___x_2423_);
    lean_ctor_set(v___x_2430_, 1, v___x_2429_);
    v___x_2431_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_2432_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_2433_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2433_, 0, v___x_2432_);
    lean_ctor_set(v___x_2433_, 1, v___x_2430_);
    v___x_2434_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_2435_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2435_, 0, v___x_2433_);
    lean_ctor_set(v___x_2435_, 1, v___x_2434_);
    v___x_2436_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2436_, 0, v___x_2431_);
    lean_ctor_set(v___x_2436_, 1, v___x_2435_);
    v___x_2437_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2437_, 0, v___x_2436_);
    lean_ctor_set_uint8(
        v___x_2437_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2428_,
    );
    return v___x_2437_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr(
    mut v_x_2438_: *mut LeanObject,
    mut v_prec_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    v___x_2440_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_x_2438_);
    return v___x_2440_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(
    mut v_x_2441_: *mut LeanObject,
    mut v_prec_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Meta_Match_instReprDiscrInfo_repr(v_x_2441_, v_prec_2442_);
    lean_dec(v_prec_2442_);
    return v_res_2443_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0() -> *mut LeanObject
{
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    v___x_2446_ = lean_box(0);
    v___x_2447_ = lean_unsigned_to_nat(16);
    v___x_2448_ = lean_mk_array(v___x_2447_, v___x_2446_);
    return v___x_2448_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1() -> *mut LeanObject
{
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2449_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once),
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0,
    );
    v___x_2450_ = lean_unsigned_to_nat(0);
    v___x_2451_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2451_, 0, v___x_2450_);
    lean_ctor_set(v___x_2451_, 1, v___x_2449_);
    return v___x_2451_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default() -> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once),
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1,
    );
    return v___x_2452_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps() -> *mut LeanObject {
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
    return v___x_2453_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(
    mut v_x_2454_: *mut LeanObject,
    mut v_x_2455_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2455_) == 0 {
        lean_inc(v_x_2454_);
        return v_x_2454_;
    } else {
        let mut v_key_2456_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_2457_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
        v_key_2456_ = lean_ctor_get(v_x_2455_, 0);
        v_value_2457_ = lean_ctor_get(v_x_2455_, 1);
        v_tail_2458_ = lean_ctor_get(v_x_2455_, 2);
        v___x_2459_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_2454_, v_tail_2458_);
        lean_inc(v_value_2457_);
        lean_inc(v_key_2456_);
        v___x_2460_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2460_, 0, v_key_2456_);
        lean_ctor_set(v___x_2460_, 1, v_value_2457_);
        v___x_2461_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2461_, 0, v___x_2460_);
        lean_ctor_set(v___x_2461_, 1, v___x_2459_);
        return v___x_2461_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(
    mut v_x_2462_: *mut LeanObject,
    mut v_x_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2464_: *mut LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_2462_, v_x_2463_);
    lean_dec(v_x_2463_);
    lean_dec(v_x_2462_);
    return v_res_2464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(
    mut v_as_2465_: *mut LeanObject,
    mut v_i_2466_: usize,
    mut v_stop_2467_: usize,
    mut v_b_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2469_ = lean_usize_dec_eq(v_i_2466_, v_stop_2467_);
                if v___x_2469_ == 0 {
                    v___x_2470_ = 1usize;
                    v___x_2471_ = lean_usize_sub(v_i_2466_, v___x_2470_);
                    v___x_2472_ = lean_array_uget_borrowed(v_as_2465_, v___x_2471_);
                    v___x_2473_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_b_2468_, v___x_2472_);
                    lean_dec(v_b_2468_);
                    v_i_2466_ = v___x_2471_;
                    v_b_2468_ = v___x_2473_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2468_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(
    mut v_as_2475_: *mut LeanObject,
    mut v_i_2476_: *mut LeanObject,
    mut v_stop_2477_: *mut LeanObject,
    mut v_b_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2479_: usize = 0;
    let mut v_stop_boxed_2480_: usize = 0;
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2479_ = lean_unbox_usize(v_i_2476_);
    lean_dec(v_i_2476_);
    v_stop_boxed_2480_ = lean_unbox_usize(v_stop_2477_);
    lean_dec(v_stop_2477_);
    v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_2475_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2478_);
    lean_dec_ref(v_as_2475_);
    return v_res_2481_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(
    mut v_x_2482_: *mut LeanObject,
    mut v_x_2483_: *mut LeanObject,
    mut v_x_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2484_) == 0 {
                    lean_dec(v_x_2482_);
                    return v_x_2483_;
                } else {
                    v_head_2485_ = lean_ctor_get(v_x_2484_, 0);
                    v_tail_2486_ = lean_ctor_get(v_x_2484_, 1);
                    v_isSharedCheck_2497_ = (!lean_is_exclusive(v_x_2484_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v___x_2488_ = v_x_2484_;
                        v_isShared_2489_ = v_isSharedCheck_2497_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2486_);
                        lean_inc(v_head_2485_);
                        lean_dec(v_x_2484_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2497_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2482_);
                if v_isShared_2489_ == 0 {
                    lean_ctor_set_tag(v___x_2488_, 5);
                    lean_ctor_set(v___x_2488_, 1, v_x_2482_);
                    lean_ctor_set(v___x_2488_, 0, v_x_2483_);
                    v___x_2491_ = v___x_2488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_x_2483_);
                    lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_x_2482_);
                    v___x_2491_ = v_reuseFailAlloc_2496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2492_ = l_Nat_reprFast(v_head_2485_);
                v___x_2493_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2493_, 0, v___x_2492_);
                v___x_2494_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2494_, 0, v___x_2491_);
                lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                v_x_2483_ = v___x_2494_;
                v_x_2484_ = v_tail_2486_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(
    mut v_x_2498_: *mut LeanObject,
    mut v_x_2499_: *mut LeanObject,
    mut v_x_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2500_) == 0 {
                    lean_dec(v_x_2498_);
                    return v_x_2499_;
                } else {
                    v_head_2501_ = lean_ctor_get(v_x_2500_, 0);
                    v_tail_2502_ = lean_ctor_get(v_x_2500_, 1);
                    v_isSharedCheck_2513_ = (!lean_is_exclusive(v_x_2500_)) as u8;
                    if v_isSharedCheck_2513_ == 0 {
                        v___x_2504_ = v_x_2500_;
                        v_isShared_2505_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2502_);
                        lean_inc(v_head_2501_);
                        lean_dec(v_x_2500_);
                        v___x_2504_ = lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2498_);
                if v_isShared_2505_ == 0 {
                    lean_ctor_set_tag(v___x_2504_, 5);
                    lean_ctor_set(v___x_2504_, 1, v_x_2498_);
                    lean_ctor_set(v___x_2504_, 0, v_x_2499_);
                    v___x_2507_ = v___x_2504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_x_2499_);
                    lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_x_2498_);
                    v___x_2507_ = v_reuseFailAlloc_2512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2508_ = l_Nat_reprFast(v_head_2501_);
                v___x_2509_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2509_, 0, v___x_2508_);
                v___x_2510_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2510_, 0, v___x_2507_);
                lean_ctor_set(v___x_2510_, 1, v___x_2509_);
                v___x_2511_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(v_x_2498_, v___x_2510_, v_tail_2502_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(
    mut v___y_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Nat_reprFast(v___y_2514_);
    v___x_2516_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2516_, 0, v___x_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(
    mut v_x_2517_: *mut LeanObject,
    mut v_x_2518_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2517_) == 0 {
        let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2518_);
        v___x_2519_ = lean_box(0);
        return v___x_2519_;
    } else {
        let mut v_tail_2520_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2520_ = lean_ctor_get(v_x_2517_, 1);
        if lean_obj_tag(v_tail_2520_) == 0 {
            let mut v_head_2521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2518_);
            v_head_2521_ = lean_ctor_get(v_x_2517_, 0);
            lean_inc(v_head_2521_);
            lean_dec_ref_known(v_x_2517_, 2);
            v___x_2522_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2521_);
            return v___x_2522_;
        } else {
            let mut v_head_2523_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2520_);
            v_head_2523_ = lean_ctor_get(v_x_2517_, 0);
            lean_inc(v_head_2523_);
            lean_dec_ref_known(v_x_2517_, 2);
            v___x_2524_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2523_);
            v___x_2525_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(v_x_2518_, v___x_2524_, v_tail_2520_);
            return v___x_2525_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_2538_ = lean_string_length(v___x_2537_);
    return v___x_2538_;
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7);
    v___x_2540_ = lean_nat_to_int(v___x_2539_);
    return v___x_2540_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(
    mut v_a_2545_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_2545_) == 0 {
        let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
        v___x_2546_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1;
        return v___x_2546_;
    } else {
        let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2555_: u8 = 0;
        let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
        v___x_2547_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_2548_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(v_a_2545_, v___x_2547_);
        v___x_2549_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
        v___x_2550_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9;
        v___x_2551_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2551_, 0, v___x_2550_);
        lean_ctor_set(v___x_2551_, 1, v___x_2548_);
        v___x_2552_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_2553_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2553_, 0, v___x_2551_);
        lean_ctor_set(v___x_2553_, 1, v___x_2552_);
        v___x_2554_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2554_, 0, v___x_2549_);
        lean_ctor_set(v___x_2554_, 1, v___x_2553_);
        v___x_2555_ = 0;
        v___x_2556_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_2556_, 0, v___x_2554_);
        lean_ctor_set_uint8(
            v___x_2556_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_2555_,
        );
        return v___x_2556_;
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(
    mut v_x_2557_: *mut LeanObject,
    mut v_x_2558_: *mut LeanObject,
    mut v_x_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2559_) == 0 {
                    lean_dec(v_x_2557_);
                    return v_x_2558_;
                } else {
                    v_head_2560_ = lean_ctor_get(v_x_2559_, 0);
                    v_tail_2561_ = lean_ctor_get(v_x_2559_, 1);
                    v_isSharedCheck_2570_ = (!lean_is_exclusive(v_x_2559_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2563_ = v_x_2559_;
                        v_isShared_2564_ = v_isSharedCheck_2570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2561_);
                        lean_inc(v_head_2560_);
                        lean_dec(v_x_2559_);
                        v___x_2563_ = lean_box(0);
                        v_isShared_2564_ = v_isSharedCheck_2570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2557_);
                if v_isShared_2564_ == 0 {
                    lean_ctor_set_tag(v___x_2563_, 5);
                    lean_ctor_set(v___x_2563_, 1, v_x_2557_);
                    lean_ctor_set(v___x_2563_, 0, v_x_2558_);
                    v___x_2566_ = v___x_2563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_x_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_x_2557_);
                    v___x_2566_ = v_reuseFailAlloc_2569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2567_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                lean_ctor_set(v___x_2567_, 1, v_head_2560_);
                v_x_2558_ = v___x_2567_;
                v_x_2559_ = v_tail_2561_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(
    mut v_x_2571_: *mut LeanObject,
    mut v_x_2572_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2571_) == 0 {
        let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2572_);
        v___x_2573_ = lean_box(0);
        return v___x_2573_;
    } else {
        let mut v_tail_2574_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2574_ = lean_ctor_get(v_x_2571_, 1);
        if lean_obj_tag(v_tail_2574_) == 0 {
            let mut v_head_2575_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2572_);
            v_head_2575_ = lean_ctor_get(v_x_2571_, 0);
            lean_inc(v_head_2575_);
            lean_dec_ref_known(v_x_2571_, 2);
            return v_head_2575_;
        } else {
            let mut v_head_2576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2574_);
            v_head_2576_ = lean_ctor_get(v_x_2571_, 0);
            lean_inc(v_head_2576_);
            lean_dec_ref_known(v_x_2571_, 2);
            v___x_2577_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(v_x_2572_, v_head_2576_, v_tail_2574_);
            return v___x_2577_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(
    mut v_init_2578_: *mut LeanObject,
    mut v_x_2579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2579_) == 0 {
                    v_k_2580_ = lean_ctor_get(v_x_2579_, 1);
                    v_l_2581_ = lean_ctor_get(v_x_2579_, 3);
                    v_r_2582_ = lean_ctor_get(v_x_2579_, 4);
                    v___x_2583_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_2578_, v_r_2582_);
                    lean_inc(v_k_2580_);
                    v___x_2584_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2584_, 0, v_k_2580_);
                    lean_ctor_set(v___x_2584_, 1, v___x_2583_);
                    v_init_2578_ = v___x_2584_;
                    v_x_2579_ = v_l_2581_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2578_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(
    mut v_init_2586_: *mut LeanObject,
    mut v_x_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2588_: *mut LeanObject = core::ptr::null_mut();
    v_res_2588_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_2586_, v_x_2587_);
    lean_dec(v_x_2587_);
    return v_res_2588_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2595_ = lean_string_length(v___x_2594_);
    return v___x_2595_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    v___x_2596_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4);
    v___x_2597_ = lean_nat_to_int(v___x_2596_);
    return v___x_2597_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(
    mut v_x_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2603_ = lean_ctor_get(v_x_2602_, 0);
                v_snd_2604_ = lean_ctor_get(v_x_2602_, 1);
                v_isSharedCheck_2632_ = (!lean_is_exclusive(v_x_2602_)) as u8;
                if v_isSharedCheck_2632_ == 0 {
                    v___x_2606_ = v_x_2602_;
                    v_isShared_2607_ = v_isSharedCheck_2632_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2604_);
                    lean_inc(v_fst_2603_);
                    lean_dec(v_x_2602_);
                    v___x_2606_ = lean_box(0);
                    v_isShared_2607_ = v_isSharedCheck_2632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2608_ = l_Nat_reprFast(v_fst_2603_);
                v___x_2609_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2609_, 0, v___x_2608_);
                v___x_2610_ = lean_box(0);
                if v_isShared_2607_ == 0 {
                    lean_ctor_set_tag(v___x_2606_, 1);
                    lean_ctor_set(v___x_2606_, 1, v___x_2610_);
                    lean_ctor_set(v___x_2606_, 0, v___x_2609_);
                    v___x_2612_ = v___x_2606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2609_);
                    lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2610_);
                    v___x_2612_ = v_reuseFailAlloc_2631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2613_ = lean_unsigned_to_nat(0);
                v___x_2614_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2;
                v___x_2615_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v___x_2610_, v_snd_2604_);
                lean_dec(v_snd_2604_);
                v___x_2616_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v___x_2615_);
                v___x_2617_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2617_, 0, v___x_2614_);
                lean_ctor_set(v___x_2617_, 1, v___x_2616_);
                v___x_2618_ = l_Repr_addAppParen(v___x_2617_, v___x_2613_);
                v___x_2619_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2619_, 0, v___x_2618_);
                lean_ctor_set(v___x_2619_, 1, v___x_2612_);
                v___x_2620_ = l_List_reverse___redArg(v___x_2619_);
                v___x_2621_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
                v___x_2622_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(v___x_2620_, v___x_2621_);
                v___x_2623_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5);
                v___x_2624_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6;
                v___x_2625_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2625_, 0, v___x_2624_);
                lean_ctor_set(v___x_2625_, 1, v___x_2622_);
                v___x_2626_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7;
                v___x_2627_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2628_, 0, v___x_2623_);
                lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = 0;
                v___x_2630_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2630_, 0, v___x_2628_);
                lean_ctor_set_uint8(
                    v___x_2630_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2629_,
                );
                return v___x_2630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(
    mut v_x_2633_: *mut LeanObject,
    mut v_x_2634_: *mut LeanObject,
    mut v_x_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2635_) == 0 {
                    lean_dec(v_x_2633_);
                    return v_x_2634_;
                } else {
                    v_head_2636_ = lean_ctor_get(v_x_2635_, 0);
                    v_tail_2637_ = lean_ctor_get(v_x_2635_, 1);
                    v_isSharedCheck_2647_ = (!lean_is_exclusive(v_x_2635_)) as u8;
                    if v_isSharedCheck_2647_ == 0 {
                        v___x_2639_ = v_x_2635_;
                        v_isShared_2640_ = v_isSharedCheck_2647_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2637_);
                        lean_inc(v_head_2636_);
                        lean_dec(v_x_2635_);
                        v___x_2639_ = lean_box(0);
                        v_isShared_2640_ = v_isSharedCheck_2647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2633_);
                if v_isShared_2640_ == 0 {
                    lean_ctor_set_tag(v___x_2639_, 5);
                    lean_ctor_set(v___x_2639_, 1, v_x_2633_);
                    lean_ctor_set(v___x_2639_, 0, v_x_2634_);
                    v___x_2642_ = v___x_2639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_x_2634_);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_x_2633_);
                    v___x_2642_ = v_reuseFailAlloc_2646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2643_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2636_);
                v___x_2644_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2644_, 0, v___x_2642_);
                lean_ctor_set(v___x_2644_, 1, v___x_2643_);
                v_x_2634_ = v___x_2644_;
                v_x_2635_ = v_tail_2637_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(
    mut v_x_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
    mut v_x_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2650_) == 0 {
                    lean_dec(v_x_2648_);
                    return v_x_2649_;
                } else {
                    v_head_2651_ = lean_ctor_get(v_x_2650_, 0);
                    v_tail_2652_ = lean_ctor_get(v_x_2650_, 1);
                    v_isSharedCheck_2662_ = (!lean_is_exclusive(v_x_2650_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2654_ = v_x_2650_;
                        v_isShared_2655_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2652_);
                        lean_inc(v_head_2651_);
                        lean_dec(v_x_2650_);
                        v___x_2654_ = lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2648_);
                if v_isShared_2655_ == 0 {
                    lean_ctor_set_tag(v___x_2654_, 5);
                    lean_ctor_set(v___x_2654_, 1, v_x_2648_);
                    lean_ctor_set(v___x_2654_, 0, v_x_2649_);
                    v___x_2657_ = v___x_2654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_x_2649_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_x_2648_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2658_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2651_);
                v___x_2659_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2659_, 0, v___x_2657_);
                lean_ctor_set(v___x_2659_, 1, v___x_2658_);
                v___x_2660_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(v_x_2648_, v___x_2659_, v_tail_2652_);
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(
    mut v_x_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2663_) == 0 {
        let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2664_);
        v___x_2665_ = lean_box(0);
        return v___x_2665_;
    } else {
        let mut v_tail_2666_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2666_ = lean_ctor_get(v_x_2663_, 1);
        if lean_obj_tag(v_tail_2666_) == 0 {
            let mut v_head_2667_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2664_);
            v_head_2667_ = lean_ctor_get(v_x_2663_, 0);
            lean_inc(v_head_2667_);
            lean_dec_ref_known(v_x_2663_, 2);
            v___x_2668_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2667_);
            return v___x_2668_;
        } else {
            let mut v_head_2669_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2666_);
            v_head_2669_ = lean_ctor_get(v_x_2663_, 0);
            lean_inc(v_head_2669_);
            lean_dec_ref_known(v_x_2663_, 2);
            v___x_2670_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2669_);
            v___x_2671_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(v_x_2664_, v___x_2670_, v_tail_2666_);
            return v___x_2671_;
        }
    }
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(
    mut v_a_2672_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_2672_) == 0 {
        let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
        v___x_2673_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1;
        return v___x_2673_;
    } else {
        let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
        v___x_2674_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_2675_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(v_a_2672_, v___x_2674_);
        v___x_2676_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
        v___x_2677_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9;
        v___x_2678_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2678_, 0, v___x_2677_);
        lean_ctor_set(v___x_2678_, 1, v___x_2675_);
        v___x_2679_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_2680_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2680_, 0, v___x_2678_);
        lean_ctor_set(v___x_2680_, 1, v___x_2679_);
        v___x_2681_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2681_, 0, v___x_2676_);
        lean_ctor_set(v___x_2681_, 1, v___x_2680_);
        v___x_2682_ = 0;
        v___x_2683_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_2683_, 0, v___x_2681_);
        lean_ctor_set_uint8(
            v___x_2683_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_2682_,
        );
        return v___x_2683_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4() -> *mut LeanObject
{
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2693_ = lean_unsigned_to_nat(7);
    v___x_2694_ = lean_nat_to_int(v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr___redArg(
    mut v_x_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    let mut v___x_2728_: usize = 0;
    let mut v___x_2729_: usize = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_unused_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2699_ = lean_ctor_get(v_x_2698_, 1);
                v_isSharedCheck_2731_ = (!lean_is_exclusive(v_x_2698_)) as u8;
                if v_isSharedCheck_2731_ == 0 {
                    v_unused_2732_ = lean_ctor_get(v_x_2698_, 0);
                    lean_dec(v_unused_2732_);
                    v___x_2701_ = v_x_2698_;
                    v_isShared_2702_ = v_isSharedCheck_2731_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2699_);
                    lean_dec(v_x_2698_);
                    v___x_2701_ = lean_box(0);
                    v_isShared_2702_ = v_isSharedCheck_2731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2703_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3;
                v___x_2704_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4,
                );
                v___x_2705_ = lean_unsigned_to_nat(0);
                v___x_2706_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6;
                v___x_2725_ = lean_box(0);
                v___x_2726_ = lean_array_get_size(v_buckets_2699_);
                v___x_2727_ = lean_nat_dec_lt(v___x_2705_, v___x_2726_);
                if v___x_2727_ == 0 {
                    lean_dec_ref(v_buckets_2699_);
                    v___y_2708_ = v___x_2725_;
                    state = 2;
                    continue;
                } else {
                    v___x_2728_ = lean_usize_of_nat(v___x_2726_);
                    v___x_2729_ = 0usize;
                    v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_buckets_2699_, v___x_2728_, v___x_2729_, v___x_2725_);
                    lean_dec_ref(v_buckets_2699_);
                    v___y_2708_ = v___x_2730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2709_ =
                    l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(
                        v___y_2708_,
                    );
                if v_isShared_2702_ == 0 {
                    lean_ctor_set_tag(v___x_2701_, 5);
                    lean_ctor_set(v___x_2701_, 1, v___x_2709_);
                    lean_ctor_set(v___x_2701_, 0, v___x_2706_);
                    v___x_2711_ = v___x_2701_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2706_);
                    lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2709_);
                    v___x_2711_ = v_reuseFailAlloc_2724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2712_ = l_Repr_addAppParen(v___x_2711_, v___x_2705_);
                v___x_2713_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2713_, 0, v___x_2704_);
                lean_ctor_set(v___x_2713_, 1, v___x_2712_);
                v___x_2714_ = 0;
                v___x_2715_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2715_, 0, v___x_2713_);
                lean_ctor_set_uint8(
                    v___x_2715_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2714_,
                );
                v___x_2716_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2716_, 0, v___x_2703_);
                lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                v___x_2717_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
                );
                v___x_2718_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
                v___x_2719_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2719_, 0, v___x_2718_);
                lean_ctor_set(v___x_2719_, 1, v___x_2716_);
                v___x_2720_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
                v___x_2721_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2721_, 0, v___x_2719_);
                lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                v___x_2722_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2722_, 0, v___x_2717_);
                lean_ctor_set(v___x_2722_, 1, v___x_2721_);
                v___x_2723_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2723_, 0, v___x_2722_);
                lean_ctor_set_uint8(
                    v___x_2723_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2714_,
                );
                return v___x_2723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr(
    mut v_x_2733_: *mut LeanObject,
    mut v_prec_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    v___x_2735_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_2733_);
    return v___x_2735_;
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr___boxed(
    mut v_x_2736_: *mut LeanObject,
    mut v_prec_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2738_: *mut LeanObject = core::ptr::null_mut();
    v_res_2738_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_2736_, v_prec_2737_);
    lean_dec(v_prec_2737_);
    return v_res_2738_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(
    mut v_a_2739_: *mut LeanObject,
    mut v_n_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    v___x_2741_ =
        l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v_a_2739_);
    return v___x_2741_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(
    mut v_a_2742_: *mut LeanObject,
    mut v_n_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2744_: *mut LeanObject = core::ptr::null_mut();
    v_res_2744_ =
        l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_a_2742_, v_n_2743_);
    lean_dec(v_n_2743_);
    return v_res_2744_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(
    mut v_x_2745_: *mut LeanObject,
    mut v_x_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    v___x_2747_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_x_2745_);
    return v___x_2747_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(
    mut v_x_2748_: *mut LeanObject,
    mut v_x_2749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2750_: *mut LeanObject = core::ptr::null_mut();
    v_res_2750_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(v_x_2748_, v_x_2749_);
    lean_dec(v_x_2749_);
    return v_res_2750_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(
    mut v_a_2751_: *mut LeanObject,
    mut v_n_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v_a_2751_);
    return v___x_2753_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(
    mut v_a_2754_: *mut LeanObject,
    mut v_n_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(v_a_2754_, v_n_2755_);
    lean_dec(v_n_2755_);
    return v_res_2756_;
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_isEmpty(mut v_o_2759_: *mut LeanObject) -> u8 {
    let mut v_size_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    v_size_2760_ = lean_ctor_get(v_o_2759_, 0);
    v___x_2761_ = lean_unsigned_to_nat(0);
    v___x_2762_ = lean_nat_dec_eq(v_size_2760_, v___x_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_isEmpty___boxed(
    mut v_o_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2764_: u8 = 0;
    let mut v_r_2765_: *mut LeanObject = core::ptr::null_mut();
    v_res_2764_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_2763_);
    lean_dec_ref(v_o_2763_);
    v_r_2765_ = lean_box((v_res_2764_) as usize);
    return v_r_2765_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(
    mut v_k_2766_: *mut LeanObject,
    mut v_t_2767_: *mut LeanObject,
) -> u8 {
    let mut v_k_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2767_) == 0 {
                    v_k_2768_ = lean_ctor_get(v_t_2767_, 1);
                    v_l_2769_ = lean_ctor_get(v_t_2767_, 3);
                    v_r_2770_ = lean_ctor_get(v_t_2767_, 4);
                    v___x_2771_ = lean_nat_dec_lt(v_k_2766_, v_k_2768_);
                    if v___x_2771_ == 0 {
                        v___x_2772_ = lean_nat_dec_eq(v_k_2766_, v_k_2768_);
                        if v___x_2772_ == 0 {
                            v_t_2767_ = v_r_2770_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2772_;
                        }
                    } else {
                        v_t_2767_ = v_l_2769_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2775_ = 0;
                    return v___x_2775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(
    mut v_k_2776_: *mut LeanObject,
    mut v_t_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2778_: u8 = 0;
    let mut v_r_2779_: *mut LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_2776_, v_t_2777_);
    lean_dec(v_t_2777_);
    lean_dec(v_k_2776_);
    v_r_2779_ = lean_box((v_res_2778_) as usize);
    return v_r_2779_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(
    mut v_k_2780_: *mut LeanObject,
    mut v_v_2781_: *mut LeanObject,
    mut v_t_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: u8 = 0;
    let mut v_impl_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v_size_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2823_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v_unused_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v_unused_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v_k_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_unused_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_unused_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_unused_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v_size_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_unused_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_unused_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3040_: u8 = 0;
    let mut v_k_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v_unused_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_unused_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2782_) == 0 {
                    v_size_2783_ = lean_ctor_get(v_t_2782_, 0);
                    v_k_2784_ = lean_ctor_get(v_t_2782_, 1);
                    v_v_2785_ = lean_ctor_get(v_t_2782_, 2);
                    v_l_2786_ = lean_ctor_get(v_t_2782_, 3);
                    v_r_2787_ = lean_ctor_get(v_t_2782_, 4);
                    v_isSharedCheck_3068_ = (!lean_is_exclusive(v_t_2782_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_2789_ = v_t_2782_;
                        v_isShared_2790_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2787_);
                        lean_inc(v_l_2786_);
                        lean_inc(v_v_2785_);
                        lean_inc(v_k_2784_);
                        lean_inc(v_size_2783_);
                        lean_dec(v_t_2782_);
                        v___x_2789_ = lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3069_ = lean_unsigned_to_nat(1);
                    v___x_3070_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3070_, 0, v___x_3069_);
                    lean_ctor_set(v___x_3070_, 1, v_k_2780_);
                    lean_ctor_set(v___x_3070_, 2, v_v_2781_);
                    lean_ctor_set(v___x_3070_, 3, v_t_2782_);
                    lean_ctor_set(v___x_3070_, 4, v_t_2782_);
                    return v___x_3070_;
                }
            }
            1 => {
                v___x_2791_ = lean_nat_dec_lt(v_k_2780_, v_k_2784_);
                if v___x_2791_ == 0 {
                    v___x_2792_ = lean_nat_dec_eq(v_k_2780_, v_k_2784_);
                    if v___x_2792_ == 0 {
                        lean_dec(v_size_2783_);
                        v_impl_2793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_2780_, v_v_2781_, v_r_2787_);
                        v___x_2794_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_2786_) == 0 {
                            v_size_2795_ = lean_ctor_get(v_l_2786_, 0);
                            v_size_2796_ = lean_ctor_get(v_impl_2793_, 0);
                            lean_inc(v_size_2796_);
                            v_k_2797_ = lean_ctor_get(v_impl_2793_, 1);
                            lean_inc(v_k_2797_);
                            v_v_2798_ = lean_ctor_get(v_impl_2793_, 2);
                            lean_inc(v_v_2798_);
                            v_l_2799_ = lean_ctor_get(v_impl_2793_, 3);
                            lean_inc(v_l_2799_);
                            v_r_2800_ = lean_ctor_get(v_impl_2793_, 4);
                            lean_inc(v_r_2800_);
                            v___x_2801_ = lean_unsigned_to_nat(3);
                            v___x_2802_ = lean_nat_mul(v___x_2801_, v_size_2795_);
                            v___x_2803_ = lean_nat_dec_lt(v___x_2802_, v_size_2796_);
                            lean_dec(v___x_2802_);
                            if v___x_2803_ == 0 {
                                lean_dec(v_r_2800_);
                                lean_dec(v_l_2799_);
                                lean_dec(v_v_2798_);
                                lean_dec(v_k_2797_);
                                v___x_2804_ = lean_nat_add(v___x_2794_, v_size_2795_);
                                v___x_2805_ = lean_nat_add(v___x_2804_, v_size_2796_);
                                lean_dec(v_size_2796_);
                                lean_dec(v___x_2804_);
                                if v_isShared_2790_ == 0 {
                                    lean_ctor_set(v___x_2789_, 4, v_impl_2793_);
                                    lean_ctor_set(v___x_2789_, 0, v___x_2805_);
                                    v___x_2807_ = v___x_2789_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
                                    lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_k_2784_);
                                    lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_v_2785_);
                                    lean_ctor_set(v_reuseFailAlloc_2808_, 3, v_l_2786_);
                                    lean_ctor_set(v_reuseFailAlloc_2808_, 4, v_impl_2793_);
                                    v___x_2807_ = v_reuseFailAlloc_2808_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2872_ = (!lean_is_exclusive(v_impl_2793_)) as u8;
                                if v_isSharedCheck_2872_ == 0 {
                                    v_unused_2873_ = lean_ctor_get(v_impl_2793_, 4);
                                    lean_dec(v_unused_2873_);
                                    v_unused_2874_ = lean_ctor_get(v_impl_2793_, 3);
                                    lean_dec(v_unused_2874_);
                                    v_unused_2875_ = lean_ctor_get(v_impl_2793_, 2);
                                    lean_dec(v_unused_2875_);
                                    v_unused_2876_ = lean_ctor_get(v_impl_2793_, 1);
                                    lean_dec(v_unused_2876_);
                                    v_unused_2877_ = lean_ctor_get(v_impl_2793_, 0);
                                    lean_dec(v_unused_2877_);
                                    v___x_2810_ = v_impl_2793_;
                                    v_isShared_2811_ = v_isSharedCheck_2872_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2793_);
                                    v___x_2810_ = lean_box(0);
                                    v_isShared_2811_ = v_isSharedCheck_2872_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2878_ = lean_ctor_get(v_impl_2793_, 3);
                            lean_inc(v_l_2878_);
                            if lean_obj_tag(v_l_2878_) == 0 {
                                v_r_2879_ = lean_ctor_get(v_impl_2793_, 4);
                                v_k_2880_ = lean_ctor_get(v_impl_2793_, 1);
                                v_v_2881_ = lean_ctor_get(v_impl_2793_, 2);
                                v_isSharedCheck_2904_ = (!lean_is_exclusive(v_impl_2793_)) as u8;
                                if v_isSharedCheck_2904_ == 0 {
                                    v_unused_2905_ = lean_ctor_get(v_impl_2793_, 3);
                                    lean_dec(v_unused_2905_);
                                    v_unused_2906_ = lean_ctor_get(v_impl_2793_, 0);
                                    lean_dec(v_unused_2906_);
                                    v___x_2883_ = v_impl_2793_;
                                    v_isShared_2884_ = v_isSharedCheck_2904_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_2879_);
                                    lean_inc(v_v_2881_);
                                    lean_inc(v_k_2880_);
                                    lean_dec(v_impl_2793_);
                                    v___x_2883_ = lean_box(0);
                                    v_isShared_2884_ = v_isSharedCheck_2904_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2907_ = lean_ctor_get(v_impl_2793_, 4);
                                lean_inc(v_r_2907_);
                                if lean_obj_tag(v_r_2907_) == 0 {
                                    v_k_2908_ = lean_ctor_get(v_impl_2793_, 1);
                                    v_v_2909_ = lean_ctor_get(v_impl_2793_, 2);
                                    v_isSharedCheck_2920_ =
                                        (!lean_is_exclusive(v_impl_2793_)) as u8;
                                    if v_isSharedCheck_2920_ == 0 {
                                        v_unused_2921_ = lean_ctor_get(v_impl_2793_, 4);
                                        lean_dec(v_unused_2921_);
                                        v_unused_2922_ = lean_ctor_get(v_impl_2793_, 3);
                                        lean_dec(v_unused_2922_);
                                        v_unused_2923_ = lean_ctor_get(v_impl_2793_, 0);
                                        lean_dec(v_unused_2923_);
                                        v___x_2911_ = v_impl_2793_;
                                        v_isShared_2912_ = v_isSharedCheck_2920_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2909_);
                                        lean_inc(v_k_2908_);
                                        lean_dec(v_impl_2793_);
                                        v___x_2911_ = lean_box(0);
                                        v_isShared_2912_ = v_isSharedCheck_2920_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_2924_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2790_ == 0 {
                                        lean_ctor_set(v___x_2789_, 4, v_impl_2793_);
                                        lean_ctor_set(v___x_2789_, 3, v_r_2907_);
                                        lean_ctor_set(v___x_2789_, 0, v___x_2924_);
                                        v___x_2926_ = v___x_2789_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
                                        lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2784_);
                                        lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2785_);
                                        lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_r_2907_);
                                        lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_impl_2793_);
                                        v___x_2926_ = v_reuseFailAlloc_2927_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_2785_);
                        lean_dec(v_k_2784_);
                        if v_isShared_2790_ == 0 {
                            lean_ctor_set(v___x_2789_, 2, v_v_2781_);
                            lean_ctor_set(v___x_2789_, 1, v_k_2780_);
                            v___x_2929_ = v___x_2789_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_size_2783_);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2780_);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2781_);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_l_2786_);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_r_2787_);
                            v___x_2929_ = v_reuseFailAlloc_2930_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_2783_);
                    v_impl_2931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_2780_, v_v_2781_, v_l_2786_);
                    v___x_2932_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_2787_) == 0 {
                        v_size_2933_ = lean_ctor_get(v_r_2787_, 0);
                        v_size_2934_ = lean_ctor_get(v_impl_2931_, 0);
                        lean_inc(v_size_2934_);
                        v_k_2935_ = lean_ctor_get(v_impl_2931_, 1);
                        lean_inc(v_k_2935_);
                        v_v_2936_ = lean_ctor_get(v_impl_2931_, 2);
                        lean_inc(v_v_2936_);
                        v_l_2937_ = lean_ctor_get(v_impl_2931_, 3);
                        lean_inc(v_l_2937_);
                        v_r_2938_ = lean_ctor_get(v_impl_2931_, 4);
                        lean_inc(v_r_2938_);
                        v___x_2939_ = lean_unsigned_to_nat(3);
                        v___x_2940_ = lean_nat_mul(v___x_2939_, v_size_2933_);
                        v___x_2941_ = lean_nat_dec_lt(v___x_2940_, v_size_2934_);
                        lean_dec(v___x_2940_);
                        if v___x_2941_ == 0 {
                            lean_dec(v_r_2938_);
                            lean_dec(v_l_2937_);
                            lean_dec(v_v_2936_);
                            lean_dec(v_k_2935_);
                            v___x_2942_ = lean_nat_add(v___x_2932_, v_size_2934_);
                            lean_dec(v_size_2934_);
                            v___x_2943_ = lean_nat_add(v___x_2942_, v_size_2933_);
                            lean_dec(v___x_2942_);
                            if v_isShared_2790_ == 0 {
                                lean_ctor_set(v___x_2789_, 3, v_impl_2931_);
                                lean_ctor_set(v___x_2789_, 0, v___x_2943_);
                                v___x_2945_ = v___x_2789_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
                                lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_k_2784_);
                                lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_v_2785_);
                                lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_impl_2931_);
                                lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_r_2787_);
                                v___x_2945_ = v_reuseFailAlloc_2946_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3012_ = (!lean_is_exclusive(v_impl_2931_)) as u8;
                            if v_isSharedCheck_3012_ == 0 {
                                v_unused_3013_ = lean_ctor_get(v_impl_2931_, 4);
                                lean_dec(v_unused_3013_);
                                v_unused_3014_ = lean_ctor_get(v_impl_2931_, 3);
                                lean_dec(v_unused_3014_);
                                v_unused_3015_ = lean_ctor_get(v_impl_2931_, 2);
                                lean_dec(v_unused_3015_);
                                v_unused_3016_ = lean_ctor_get(v_impl_2931_, 1);
                                lean_dec(v_unused_3016_);
                                v_unused_3017_ = lean_ctor_get(v_impl_2931_, 0);
                                lean_dec(v_unused_3017_);
                                v___x_2948_ = v_impl_2931_;
                                v_isShared_2949_ = v_isSharedCheck_3012_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_2931_);
                                v___x_2948_ = lean_box(0);
                                v_isShared_2949_ = v_isSharedCheck_3012_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3018_ = lean_ctor_get(v_impl_2931_, 3);
                        lean_inc(v_l_3018_);
                        if lean_obj_tag(v_l_3018_) == 0 {
                            v_r_3019_ = lean_ctor_get(v_impl_2931_, 4);
                            v_k_3020_ = lean_ctor_get(v_impl_2931_, 1);
                            v_v_3021_ = lean_ctor_get(v_impl_2931_, 2);
                            v_isSharedCheck_3032_ = (!lean_is_exclusive(v_impl_2931_)) as u8;
                            if v_isSharedCheck_3032_ == 0 {
                                v_unused_3033_ = lean_ctor_get(v_impl_2931_, 3);
                                lean_dec(v_unused_3033_);
                                v_unused_3034_ = lean_ctor_get(v_impl_2931_, 0);
                                lean_dec(v_unused_3034_);
                                v___x_3023_ = v_impl_2931_;
                                v_isShared_3024_ = v_isSharedCheck_3032_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_3019_);
                                lean_inc(v_v_3021_);
                                lean_inc(v_k_3020_);
                                lean_dec(v_impl_2931_);
                                v___x_3023_ = lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3032_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3035_ = lean_ctor_get(v_impl_2931_, 4);
                            lean_inc(v_r_3035_);
                            if lean_obj_tag(v_r_3035_) == 0 {
                                v_k_3036_ = lean_ctor_get(v_impl_2931_, 1);
                                v_v_3037_ = lean_ctor_get(v_impl_2931_, 2);
                                v_isSharedCheck_3060_ = (!lean_is_exclusive(v_impl_2931_)) as u8;
                                if v_isSharedCheck_3060_ == 0 {
                                    v_unused_3061_ = lean_ctor_get(v_impl_2931_, 4);
                                    lean_dec(v_unused_3061_);
                                    v_unused_3062_ = lean_ctor_get(v_impl_2931_, 3);
                                    lean_dec(v_unused_3062_);
                                    v_unused_3063_ = lean_ctor_get(v_impl_2931_, 0);
                                    lean_dec(v_unused_3063_);
                                    v___x_3039_ = v_impl_2931_;
                                    v_isShared_3040_ = v_isSharedCheck_3060_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_3037_);
                                    lean_inc(v_k_3036_);
                                    lean_dec(v_impl_2931_);
                                    v___x_3039_ = lean_box(0);
                                    v_isShared_3040_ = v_isSharedCheck_3060_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3064_ = lean_unsigned_to_nat(2);
                                if v_isShared_2790_ == 0 {
                                    lean_ctor_set(v___x_2789_, 4, v_r_3035_);
                                    lean_ctor_set(v___x_2789_, 3, v_impl_2931_);
                                    lean_ctor_set(v___x_2789_, 0, v___x_3064_);
                                    v___x_3066_ = v___x_2789_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
                                    lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_k_2784_);
                                    lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_v_2785_);
                                    lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_impl_2931_);
                                    lean_ctor_set(v_reuseFailAlloc_3067_, 4, v_r_3035_);
                                    v___x_3066_ = v_reuseFailAlloc_3067_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2807_;
            }
            3 => {
                v_size_2812_ = lean_ctor_get(v_l_2799_, 0);
                v_k_2813_ = lean_ctor_get(v_l_2799_, 1);
                v_v_2814_ = lean_ctor_get(v_l_2799_, 2);
                v_l_2815_ = lean_ctor_get(v_l_2799_, 3);
                v_r_2816_ = lean_ctor_get(v_l_2799_, 4);
                v_size_2817_ = lean_ctor_get(v_r_2800_, 0);
                v___x_2818_ = lean_unsigned_to_nat(2);
                v___x_2819_ = lean_nat_mul(v___x_2818_, v_size_2817_);
                v___x_2820_ = lean_nat_dec_lt(v_size_2812_, v___x_2819_);
                lean_dec(v___x_2819_);
                if v___x_2820_ == 0 {
                    lean_inc(v_r_2816_);
                    lean_inc(v_l_2815_);
                    lean_inc(v_v_2814_);
                    lean_inc(v_k_2813_);
                    v_isSharedCheck_2848_ = (!lean_is_exclusive(v_l_2799_)) as u8;
                    if v_isSharedCheck_2848_ == 0 {
                        v_unused_2849_ = lean_ctor_get(v_l_2799_, 4);
                        lean_dec(v_unused_2849_);
                        v_unused_2850_ = lean_ctor_get(v_l_2799_, 3);
                        lean_dec(v_unused_2850_);
                        v_unused_2851_ = lean_ctor_get(v_l_2799_, 2);
                        lean_dec(v_unused_2851_);
                        v_unused_2852_ = lean_ctor_get(v_l_2799_, 1);
                        lean_dec(v_unused_2852_);
                        v_unused_2853_ = lean_ctor_get(v_l_2799_, 0);
                        lean_dec(v_unused_2853_);
                        v___x_2822_ = v_l_2799_;
                        v_isShared_2823_ = v_isSharedCheck_2848_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_2799_);
                        v___x_2822_ = lean_box(0);
                        v_isShared_2823_ = v_isSharedCheck_2848_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2789_);
                    v___x_2854_ = lean_nat_add(v___x_2794_, v_size_2795_);
                    v___x_2855_ = lean_nat_add(v___x_2854_, v_size_2796_);
                    lean_dec(v_size_2796_);
                    v___x_2856_ = lean_nat_add(v___x_2854_, v_size_2812_);
                    lean_dec(v___x_2854_);
                    lean_inc_ref(v_l_2786_);
                    if v_isShared_2811_ == 0 {
                        lean_ctor_set(v___x_2810_, 4, v_l_2799_);
                        lean_ctor_set(v___x_2810_, 3, v_l_2786_);
                        lean_ctor_set(v___x_2810_, 2, v_v_2785_);
                        lean_ctor_set(v___x_2810_, 1, v_k_2784_);
                        lean_ctor_set(v___x_2810_, 0, v___x_2856_);
                        v___x_2858_ = v___x_2810_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2856_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2784_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2785_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_l_2786_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_l_2799_);
                        v___x_2858_ = v_reuseFailAlloc_2871_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2824_ = lean_nat_add(v___x_2794_, v_size_2795_);
                v___x_2825_ = lean_nat_add(v___x_2824_, v_size_2796_);
                lean_dec(v_size_2796_);
                if lean_obj_tag(v_l_2815_) == 0 {
                    v_size_2846_ = lean_ctor_get(v_l_2815_, 0);
                    lean_inc(v_size_2846_);
                    v___y_2838_ = v_size_2846_;
                    state = 8;
                    continue;
                } else {
                    v___x_2847_ = lean_unsigned_to_nat(0);
                    v___y_2838_ = v___x_2847_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2830_ = lean_nat_add(v___y_2828_, v___y_2829_);
                lean_dec(v___y_2829_);
                lean_dec(v___y_2828_);
                if v_isShared_2823_ == 0 {
                    lean_ctor_set(v___x_2822_, 4, v_r_2800_);
                    lean_ctor_set(v___x_2822_, 3, v_r_2816_);
                    lean_ctor_set(v___x_2822_, 2, v_v_2798_);
                    lean_ctor_set(v___x_2822_, 1, v_k_2797_);
                    lean_ctor_set(v___x_2822_, 0, v___x_2830_);
                    v___x_2832_ = v___x_2822_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2830_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_k_2797_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_v_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_r_2816_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_r_2800_);
                    v___x_2832_ = v_reuseFailAlloc_2836_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2811_ == 0 {
                    lean_ctor_set(v___x_2810_, 4, v___x_2832_);
                    lean_ctor_set(v___x_2810_, 3, v___y_2827_);
                    lean_ctor_set(v___x_2810_, 2, v_v_2814_);
                    lean_ctor_set(v___x_2810_, 1, v_k_2813_);
                    lean_ctor_set(v___x_2810_, 0, v___x_2825_);
                    v___x_2834_ = v___x_2810_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2825_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_k_2813_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_v_2814_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 3, v___y_2827_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 4, v___x_2832_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2834_;
            }
            8 => {
                v___x_2839_ = lean_nat_add(v___x_2824_, v___y_2838_);
                lean_dec(v___y_2838_);
                lean_dec(v___x_2824_);
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v_l_2815_);
                    lean_ctor_set(v___x_2789_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2789_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2839_);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2786_);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_l_2815_);
                    v___x_2841_ = v_reuseFailAlloc_2845_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2842_ = lean_nat_add(v___x_2794_, v_size_2817_);
                if lean_obj_tag(v_r_2816_) == 0 {
                    v_size_2843_ = lean_ctor_get(v_r_2816_, 0);
                    lean_inc(v_size_2843_);
                    v___y_2827_ = v___x_2841_;
                    v___y_2828_ = v___x_2842_;
                    v___y_2829_ = v_size_2843_;
                    state = 5;
                    continue;
                } else {
                    v___x_2844_ = lean_unsigned_to_nat(0);
                    v___y_2827_ = v___x_2841_;
                    v___y_2828_ = v___x_2842_;
                    v___y_2829_ = v___x_2844_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2865_ = (!lean_is_exclusive(v_l_2786_)) as u8;
                if v_isSharedCheck_2865_ == 0 {
                    v_unused_2866_ = lean_ctor_get(v_l_2786_, 4);
                    lean_dec(v_unused_2866_);
                    v_unused_2867_ = lean_ctor_get(v_l_2786_, 3);
                    lean_dec(v_unused_2867_);
                    v_unused_2868_ = lean_ctor_get(v_l_2786_, 2);
                    lean_dec(v_unused_2868_);
                    v_unused_2869_ = lean_ctor_get(v_l_2786_, 1);
                    lean_dec(v_unused_2869_);
                    v_unused_2870_ = lean_ctor_get(v_l_2786_, 0);
                    lean_dec(v_unused_2870_);
                    v___x_2860_ = v_l_2786_;
                    v_isShared_2861_ = v_isSharedCheck_2865_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_2786_);
                    v___x_2860_ = lean_box(0);
                    v_isShared_2861_ = v_isSharedCheck_2865_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2861_ == 0 {
                    lean_ctor_set(v___x_2860_, 4, v_r_2800_);
                    lean_ctor_set(v___x_2860_, 3, v___x_2858_);
                    lean_ctor_set(v___x_2860_, 2, v_v_2798_);
                    lean_ctor_set(v___x_2860_, 1, v_k_2797_);
                    lean_ctor_set(v___x_2860_, 0, v___x_2855_);
                    v___x_2863_ = v___x_2860_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2855_);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_k_2797_);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_v_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 3, v___x_2858_);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 4, v_r_2800_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2863_;
            }
            13 => {
                v_k_2885_ = lean_ctor_get(v_l_2878_, 1);
                v_v_2886_ = lean_ctor_get(v_l_2878_, 2);
                v_isSharedCheck_2900_ = (!lean_is_exclusive(v_l_2878_)) as u8;
                if v_isSharedCheck_2900_ == 0 {
                    v_unused_2901_ = lean_ctor_get(v_l_2878_, 4);
                    lean_dec(v_unused_2901_);
                    v_unused_2902_ = lean_ctor_get(v_l_2878_, 3);
                    lean_dec(v_unused_2902_);
                    v_unused_2903_ = lean_ctor_get(v_l_2878_, 0);
                    lean_dec(v_unused_2903_);
                    v___x_2888_ = v_l_2878_;
                    v_isShared_2889_ = v_isSharedCheck_2900_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_2886_);
                    lean_inc(v_k_2885_);
                    lean_dec(v_l_2878_);
                    v___x_2888_ = lean_box(0);
                    v_isShared_2889_ = v_isSharedCheck_2900_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2890_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_2879_, 2);
                if v_isShared_2889_ == 0 {
                    lean_ctor_set(v___x_2888_, 4, v_r_2879_);
                    lean_ctor_set(v___x_2888_, 3, v_r_2879_);
                    lean_ctor_set(v___x_2888_, 2, v_v_2785_);
                    lean_ctor_set(v___x_2888_, 1, v_k_2784_);
                    lean_ctor_set(v___x_2888_, 0, v___x_2794_);
                    v___x_2892_ = v___x_2888_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_r_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_r_2879_);
                    v___x_2892_ = v_reuseFailAlloc_2899_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_2879_);
                if v_isShared_2884_ == 0 {
                    lean_ctor_set(v___x_2883_, 3, v_r_2879_);
                    lean_ctor_set(v___x_2883_, 0, v___x_2794_);
                    v___x_2894_ = v___x_2883_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_k_2880_);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_v_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_r_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_r_2879_);
                    v___x_2894_ = v_reuseFailAlloc_2898_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v___x_2894_);
                    lean_ctor_set(v___x_2789_, 3, v___x_2892_);
                    lean_ctor_set(v___x_2789_, 2, v_v_2886_);
                    lean_ctor_set(v___x_2789_, 1, v_k_2885_);
                    lean_ctor_set(v___x_2789_, 0, v___x_2890_);
                    v___x_2896_ = v___x_2789_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2890_);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_k_2885_);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_v_2886_);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 3, v___x_2892_);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 4, v___x_2894_);
                    v___x_2896_ = v_reuseFailAlloc_2897_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2896_;
            }
            18 => {
                v___x_2913_ = lean_unsigned_to_nat(3);
                if v_isShared_2912_ == 0 {
                    lean_ctor_set(v___x_2911_, 4, v_l_2878_);
                    lean_ctor_set(v___x_2911_, 2, v_v_2785_);
                    lean_ctor_set(v___x_2911_, 1, v_k_2784_);
                    lean_ctor_set(v___x_2911_, 0, v___x_2794_);
                    v___x_2915_ = v___x_2911_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_l_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_l_2878_);
                    v___x_2915_ = v_reuseFailAlloc_2919_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v_r_2907_);
                    lean_ctor_set(v___x_2789_, 3, v___x_2915_);
                    lean_ctor_set(v___x_2789_, 2, v_v_2909_);
                    lean_ctor_set(v___x_2789_, 1, v_k_2908_);
                    lean_ctor_set(v___x_2789_, 0, v___x_2913_);
                    v___x_2917_ = v___x_2789_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_k_2908_);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_v_2909_);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 3, v___x_2915_);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_r_2907_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2917_;
            }
            21 => {
                return v___x_2926_;
            }
            22 => {
                return v___x_2929_;
            }
            23 => {
                return v___x_2945_;
            }
            24 => {
                v_size_2950_ = lean_ctor_get(v_l_2937_, 0);
                v_size_2951_ = lean_ctor_get(v_r_2938_, 0);
                v_k_2952_ = lean_ctor_get(v_r_2938_, 1);
                v_v_2953_ = lean_ctor_get(v_r_2938_, 2);
                v_l_2954_ = lean_ctor_get(v_r_2938_, 3);
                v_r_2955_ = lean_ctor_get(v_r_2938_, 4);
                v___x_2956_ = lean_unsigned_to_nat(2);
                v___x_2957_ = lean_nat_mul(v___x_2956_, v_size_2950_);
                v___x_2958_ = lean_nat_dec_lt(v_size_2951_, v___x_2957_);
                lean_dec(v___x_2957_);
                if v___x_2958_ == 0 {
                    lean_inc(v_r_2955_);
                    lean_inc(v_l_2954_);
                    lean_inc(v_v_2953_);
                    lean_inc(v_k_2952_);
                    v_isSharedCheck_2987_ = (!lean_is_exclusive(v_r_2938_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v_unused_2988_ = lean_ctor_get(v_r_2938_, 4);
                        lean_dec(v_unused_2988_);
                        v_unused_2989_ = lean_ctor_get(v_r_2938_, 3);
                        lean_dec(v_unused_2989_);
                        v_unused_2990_ = lean_ctor_get(v_r_2938_, 2);
                        lean_dec(v_unused_2990_);
                        v_unused_2991_ = lean_ctor_get(v_r_2938_, 1);
                        lean_dec(v_unused_2991_);
                        v_unused_2992_ = lean_ctor_get(v_r_2938_, 0);
                        lean_dec(v_unused_2992_);
                        v___x_2960_ = v_r_2938_;
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_2938_);
                        v___x_2960_ = lean_box(0);
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2789_);
                    v___x_2993_ = lean_nat_add(v___x_2932_, v_size_2934_);
                    lean_dec(v_size_2934_);
                    v___x_2994_ = lean_nat_add(v___x_2993_, v_size_2933_);
                    lean_dec(v___x_2993_);
                    v___x_2995_ = lean_nat_add(v___x_2932_, v_size_2933_);
                    v___x_2996_ = lean_nat_add(v___x_2995_, v_size_2951_);
                    lean_dec(v___x_2995_);
                    lean_inc_ref(v_r_2787_);
                    if v_isShared_2949_ == 0 {
                        lean_ctor_set(v___x_2948_, 4, v_r_2787_);
                        lean_ctor_set(v___x_2948_, 3, v_r_2938_);
                        lean_ctor_set(v___x_2948_, 2, v_v_2785_);
                        lean_ctor_set(v___x_2948_, 1, v_k_2784_);
                        lean_ctor_set(v___x_2948_, 0, v___x_2996_);
                        v___x_2998_ = v___x_2948_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2996_);
                        lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2784_);
                        lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_2785_);
                        lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_r_2938_);
                        lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_r_2787_);
                        v___x_2998_ = v_reuseFailAlloc_3011_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2962_ = lean_nat_add(v___x_2932_, v_size_2934_);
                lean_dec(v_size_2934_);
                v___x_2963_ = lean_nat_add(v___x_2962_, v_size_2933_);
                lean_dec(v___x_2962_);
                v___x_2975_ = lean_nat_add(v___x_2932_, v_size_2950_);
                if lean_obj_tag(v_l_2954_) == 0 {
                    v_size_2985_ = lean_ctor_get(v_l_2954_, 0);
                    lean_inc(v_size_2985_);
                    v___y_2977_ = v_size_2985_;
                    state = 29;
                    continue;
                } else {
                    v___x_2986_ = lean_unsigned_to_nat(0);
                    v___y_2977_ = v___x_2986_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2968_ = lean_nat_add(v___y_2965_, v___y_2967_);
                lean_dec(v___y_2967_);
                lean_dec(v___y_2965_);
                if v_isShared_2961_ == 0 {
                    lean_ctor_set(v___x_2960_, 4, v_r_2787_);
                    lean_ctor_set(v___x_2960_, 3, v_r_2955_);
                    lean_ctor_set(v___x_2960_, 2, v_v_2785_);
                    lean_ctor_set(v___x_2960_, 1, v_k_2784_);
                    lean_ctor_set(v___x_2960_, 0, v___x_2968_);
                    v___x_2970_ = v___x_2960_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2968_);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_r_2955_);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_r_2787_);
                    v___x_2970_ = v_reuseFailAlloc_2974_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2949_ == 0 {
                    lean_ctor_set(v___x_2948_, 4, v___x_2970_);
                    lean_ctor_set(v___x_2948_, 3, v___y_2966_);
                    lean_ctor_set(v___x_2948_, 2, v_v_2953_);
                    lean_ctor_set(v___x_2948_, 1, v_k_2952_);
                    lean_ctor_set(v___x_2948_, 0, v___x_2963_);
                    v___x_2972_ = v___x_2948_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2963_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_k_2952_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_v_2953_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___y_2966_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2972_;
            }
            29 => {
                v___x_2978_ = lean_nat_add(v___x_2975_, v___y_2977_);
                lean_dec(v___y_2977_);
                lean_dec(v___x_2975_);
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v_l_2954_);
                    lean_ctor_set(v___x_2789_, 3, v_l_2937_);
                    lean_ctor_set(v___x_2789_, 2, v_v_2936_);
                    lean_ctor_set(v___x_2789_, 1, v_k_2935_);
                    lean_ctor_set(v___x_2789_, 0, v___x_2978_);
                    v___x_2980_ = v___x_2789_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_k_2935_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_v_2936_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_l_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_l_2954_);
                    v___x_2980_ = v_reuseFailAlloc_2984_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2981_ = lean_nat_add(v___x_2932_, v_size_2933_);
                if lean_obj_tag(v_r_2955_) == 0 {
                    v_size_2982_ = lean_ctor_get(v_r_2955_, 0);
                    lean_inc(v_size_2982_);
                    v___y_2965_ = v___x_2981_;
                    v___y_2966_ = v___x_2980_;
                    v___y_2967_ = v_size_2982_;
                    state = 26;
                    continue;
                } else {
                    v___x_2983_ = lean_unsigned_to_nat(0);
                    v___y_2965_ = v___x_2981_;
                    v___y_2966_ = v___x_2980_;
                    v___y_2967_ = v___x_2983_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3005_ = (!lean_is_exclusive(v_r_2787_)) as u8;
                if v_isSharedCheck_3005_ == 0 {
                    v_unused_3006_ = lean_ctor_get(v_r_2787_, 4);
                    lean_dec(v_unused_3006_);
                    v_unused_3007_ = lean_ctor_get(v_r_2787_, 3);
                    lean_dec(v_unused_3007_);
                    v_unused_3008_ = lean_ctor_get(v_r_2787_, 2);
                    lean_dec(v_unused_3008_);
                    v_unused_3009_ = lean_ctor_get(v_r_2787_, 1);
                    lean_dec(v_unused_3009_);
                    v_unused_3010_ = lean_ctor_get(v_r_2787_, 0);
                    lean_dec(v_unused_3010_);
                    v___x_3000_ = v_r_2787_;
                    v_isShared_3001_ = v_isSharedCheck_3005_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_2787_);
                    v___x_3000_ = lean_box(0);
                    v_isShared_3001_ = v_isSharedCheck_3005_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3001_ == 0 {
                    lean_ctor_set(v___x_3000_, 4, v___x_2998_);
                    lean_ctor_set(v___x_3000_, 3, v_l_2937_);
                    lean_ctor_set(v___x_3000_, 2, v_v_2936_);
                    lean_ctor_set(v___x_3000_, 1, v_k_2935_);
                    lean_ctor_set(v___x_3000_, 0, v___x_2994_);
                    v___x_3003_ = v___x_3000_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2994_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_k_2935_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_v_2936_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_l_2937_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 4, v___x_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3003_;
            }
            34 => {
                v___x_3025_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3019_);
                if v_isShared_3024_ == 0 {
                    lean_ctor_set(v___x_3023_, 3, v_r_3019_);
                    lean_ctor_set(v___x_3023_, 2, v_v_2785_);
                    lean_ctor_set(v___x_3023_, 1, v_k_2784_);
                    lean_ctor_set(v___x_3023_, 0, v___x_2932_);
                    v___x_3027_ = v___x_3023_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_2932_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_r_3019_);
                    lean_ctor_set(v_reuseFailAlloc_3031_, 4, v_r_3019_);
                    v___x_3027_ = v_reuseFailAlloc_3031_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v___x_3027_);
                    lean_ctor_set(v___x_2789_, 3, v_l_3018_);
                    lean_ctor_set(v___x_2789_, 2, v_v_3021_);
                    lean_ctor_set(v___x_2789_, 1, v_k_3020_);
                    lean_ctor_set(v___x_2789_, 0, v___x_3025_);
                    v___x_3029_ = v___x_2789_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_k_3020_);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_v_3021_);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_l_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 4, v___x_3027_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3029_;
            }
            37 => {
                v_k_3041_ = lean_ctor_get(v_r_3035_, 1);
                v_v_3042_ = lean_ctor_get(v_r_3035_, 2);
                v_isSharedCheck_3056_ = (!lean_is_exclusive(v_r_3035_)) as u8;
                if v_isSharedCheck_3056_ == 0 {
                    v_unused_3057_ = lean_ctor_get(v_r_3035_, 4);
                    lean_dec(v_unused_3057_);
                    v_unused_3058_ = lean_ctor_get(v_r_3035_, 3);
                    lean_dec(v_unused_3058_);
                    v_unused_3059_ = lean_ctor_get(v_r_3035_, 0);
                    lean_dec(v_unused_3059_);
                    v___x_3044_ = v_r_3035_;
                    v_isShared_3045_ = v_isSharedCheck_3056_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_3042_);
                    lean_inc(v_k_3041_);
                    lean_dec(v_r_3035_);
                    v___x_3044_ = lean_box(0);
                    v_isShared_3045_ = v_isSharedCheck_3056_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3046_ = lean_unsigned_to_nat(3);
                if v_isShared_3045_ == 0 {
                    lean_ctor_set(v___x_3044_, 4, v_l_3018_);
                    lean_ctor_set(v___x_3044_, 3, v_l_3018_);
                    lean_ctor_set(v___x_3044_, 2, v_v_3037_);
                    lean_ctor_set(v___x_3044_, 1, v_k_3036_);
                    lean_ctor_set(v___x_3044_, 0, v___x_2932_);
                    v___x_3048_ = v___x_3044_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_2932_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_3036_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_3037_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_l_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_l_3018_);
                    v___x_3048_ = v_reuseFailAlloc_3055_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3040_ == 0 {
                    lean_ctor_set(v___x_3039_, 4, v_l_3018_);
                    lean_ctor_set(v___x_3039_, 2, v_v_2785_);
                    lean_ctor_set(v___x_3039_, 1, v_k_2784_);
                    lean_ctor_set(v___x_3039_, 0, v___x_2932_);
                    v___x_3050_ = v___x_3039_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_2932_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_k_2784_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_v_2785_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_l_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_l_3018_);
                    v___x_3050_ = v_reuseFailAlloc_3054_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 4, v___x_3050_);
                    lean_ctor_set(v___x_2789_, 3, v___x_3048_);
                    lean_ctor_set(v___x_2789_, 2, v_v_3042_);
                    lean_ctor_set(v___x_2789_, 1, v_k_3041_);
                    lean_ctor_set(v___x_2789_, 0, v___x_3046_);
                    v___x_3052_ = v___x_2789_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3046_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_k_3041_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_v_3042_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 3, v___x_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 4, v___x_3050_);
                    v___x_3052_ = v_reuseFailAlloc_3053_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3052_;
            }
            42 => {
                return v___x_3066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(
    mut v_overlapping_3071_: *mut LeanObject,
    mut v_s_x3f_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_x3f_3072_) == 0 {
                    v___x_3080_ = lean_box(1);
                    v___y_3074_ = v___x_3080_;
                    state = 1;
                    continue;
                } else {
                    v_val_3081_ = lean_ctor_get(v_s_x3f_3072_, 0);
                    lean_inc(v_val_3081_);
                    lean_dec_ref_known(v_s_x3f_3072_, 1);
                    v___y_3074_ = v_val_3081_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3075_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_3071_, v___y_3074_);
                if v___x_3075_ == 0 {
                    v___x_3076_ = lean_box(0);
                    v___x_3077_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_3071_, v___x_3076_, v___y_3074_);
                    v___x_3078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3078_, 0, v___x_3077_);
                    return v___x_3078_;
                } else {
                    lean_dec(v_overlapping_3071_);
                    v___x_3079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3079_, 0, v___y_3074_);
                    return v___x_3079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(
    mut v_overlapping_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_x_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v_tail_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3084_) == 0 {
                    v___x_3085_ = lean_box(0);
                    v___x_3086_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_3082_, v___x_3085_);
                    v_val_3087_ = lean_ctor_get(v___x_3086_, 0);
                    lean_inc(v_val_3087_);
                    lean_dec(v___x_3086_);
                    v___x_3088_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3088_, 0, v_a_3083_);
                    lean_ctor_set(v___x_3088_, 1, v_val_3087_);
                    lean_ctor_set(v___x_3088_, 2, v_x_3084_);
                    return v___x_3088_;
                } else {
                    v_key_3089_ = lean_ctor_get(v_x_3084_, 0);
                    v_value_3090_ = lean_ctor_get(v_x_3084_, 1);
                    v_tail_3091_ = lean_ctor_get(v_x_3084_, 2);
                    v_isSharedCheck_3106_ = (!lean_is_exclusive(v_x_3084_)) as u8;
                    if v_isSharedCheck_3106_ == 0 {
                        v___x_3093_ = v_x_3084_;
                        v_isShared_3094_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3091_);
                        lean_inc(v_value_3090_);
                        lean_inc(v_key_3089_);
                        lean_dec(v_x_3084_);
                        v___x_3093_ = lean_box(0);
                        v_isShared_3094_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3095_ = lean_nat_dec_eq(v_key_3089_, v_a_3083_);
                if v___x_3095_ == 0 {
                    v_tail_3096_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_3082_, v_a_3083_, v_tail_3091_);
                    if v_isShared_3094_ == 0 {
                        lean_ctor_set(v___x_3093_, 2, v_tail_3096_);
                        v___x_3098_ = v___x_3093_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_key_3089_);
                        lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_value_3090_);
                        lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_tail_3096_);
                        v___x_3098_ = v_reuseFailAlloc_3099_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_3089_);
                    v___x_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3100_, 0, v_value_3090_);
                    v___x_3101_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_3082_, v___x_3100_);
                    v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
                    lean_inc(v_val_3102_);
                    lean_dec(v___x_3101_);
                    if v_isShared_3094_ == 0 {
                        lean_ctor_set(v___x_3093_, 1, v_val_3102_);
                        lean_ctor_set(v___x_3093_, 0, v_a_3083_);
                        v___x_3104_ = v___x_3093_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3083_);
                        lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_val_3102_);
                        lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_tail_3091_);
                        v___x_3104_ = v_reuseFailAlloc_3105_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3098_;
            }
            3 => {
                return v___x_3104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(
    mut v_a_3107_: *mut LeanObject,
    mut v_x_3108_: *mut LeanObject,
) -> u8 {
    let mut v___x_3109_: u8 = 0;
    let mut v_key_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3108_) == 0 {
                    v___x_3109_ = 0;
                    return v___x_3109_;
                } else {
                    v_key_3110_ = lean_ctor_get(v_x_3108_, 0);
                    v_tail_3111_ = lean_ctor_get(v_x_3108_, 2);
                    v___x_3112_ = lean_nat_dec_eq(v_key_3110_, v_a_3107_);
                    if v___x_3112_ == 0 {
                        v_x_3108_ = v_tail_3111_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3112_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(
    mut v_a_3114_: *mut LeanObject,
    mut v_x_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3116_: u8 = 0;
    let mut v_r_3117_: *mut LeanObject = core::ptr::null_mut();
    v_res_3116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3114_, v_x_3115_);
    lean_dec(v_x_3115_);
    lean_dec(v_a_3114_);
    v_r_3117_ = lean_box((v_res_3116_) as usize);
    return v_r_3117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_x_3118_: *mut LeanObject,
    mut v_x_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u64 = 0;
    let mut v___x_3128_: u64 = 0;
    let mut v___x_3129_: u64 = 0;
    let mut v_fold_3130_: u64 = 0;
    let mut v___x_3131_: u64 = 0;
    let mut v___x_3132_: u64 = 0;
    let mut v___x_3133_: u64 = 0;
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: usize = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: usize = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3119_) == 0 {
                    return v_x_3118_;
                } else {
                    v_key_3120_ = lean_ctor_get(v_x_3119_, 0);
                    v_value_3121_ = lean_ctor_get(v_x_3119_, 1);
                    v_tail_3122_ = lean_ctor_get(v_x_3119_, 2);
                    v_isSharedCheck_3145_ = (!lean_is_exclusive(v_x_3119_)) as u8;
                    if v_isSharedCheck_3145_ == 0 {
                        v___x_3124_ = v_x_3119_;
                        v_isShared_3125_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3122_);
                        lean_inc(v_value_3121_);
                        lean_inc(v_key_3120_);
                        lean_dec(v_x_3119_);
                        v___x_3124_ = lean_box(0);
                        v_isShared_3125_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3126_ = lean_array_get_size(v_x_3118_);
                v___x_3127_ = lean_uint64_of_nat(v_key_3120_);
                v___x_3128_ = 32u64;
                v___x_3129_ = lean_uint64_shift_right(v___x_3127_, v___x_3128_);
                v_fold_3130_ = lean_uint64_xor(v___x_3127_, v___x_3129_);
                v___x_3131_ = 16u64;
                v___x_3132_ = lean_uint64_shift_right(v_fold_3130_, v___x_3131_);
                v___x_3133_ = lean_uint64_xor(v_fold_3130_, v___x_3132_);
                v___x_3134_ = lean_uint64_to_usize(v___x_3133_);
                v___x_3135_ = lean_usize_of_nat(v___x_3126_);
                v___x_3136_ = 1usize;
                v___x_3137_ = lean_usize_sub(v___x_3135_, v___x_3136_);
                v___x_3138_ = lean_usize_land(v___x_3134_, v___x_3137_);
                v___x_3139_ = lean_array_uget_borrowed(v_x_3118_, v___x_3138_);
                lean_inc(v___x_3139_);
                if v_isShared_3125_ == 0 {
                    lean_ctor_set(v___x_3124_, 2, v___x_3139_);
                    v___x_3141_ = v___x_3124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_key_3120_);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_value_3121_);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3139_);
                    v___x_3141_ = v_reuseFailAlloc_3144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3142_ = lean_array_uset(v_x_3118_, v___x_3138_, v___x_3141_);
                v_x_3118_ = v___x_3142_;
                v_x_3119_ = v_tail_3122_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(
    mut v_i_3146_: *mut LeanObject,
    mut v_source_3147_: *mut LeanObject,
    mut v_target_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v_es_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3149_ = lean_array_get_size(v_source_3147_);
                v___x_3150_ = lean_nat_dec_lt(v_i_3146_, v___x_3149_);
                if v___x_3150_ == 0 {
                    lean_dec_ref(v_source_3147_);
                    lean_dec(v_i_3146_);
                    return v_target_3148_;
                } else {
                    v_es_3151_ = lean_array_fget(v_source_3147_, v_i_3146_);
                    v___x_3152_ = lean_box(0);
                    v_source_3153_ = lean_array_fset(v_source_3147_, v_i_3146_, v___x_3152_);
                    v_target_3154_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_target_3148_, v_es_3151_);
                    v___x_3155_ = lean_unsigned_to_nat(1);
                    v___x_3156_ = lean_nat_add(v_i_3146_, v___x_3155_);
                    lean_dec(v_i_3146_);
                    v_i_3146_ = v___x_3156_;
                    v_source_3147_ = v_source_3153_;
                    v_target_3148_ = v_target_3154_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(
    mut v_data_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    v___x_3159_ = lean_array_get_size(v_data_3158_);
    v___x_3160_ = lean_unsigned_to_nat(2);
    v_nbuckets_3161_ = lean_nat_mul(v___x_3159_, v___x_3160_);
    v___x_3162_ = lean_unsigned_to_nat(0);
    v___x_3163_ = lean_box(0);
    v___x_3164_ = lean_mk_array(v_nbuckets_3161_, v___x_3163_);
    v___x_3165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v___x_3162_, v_data_3158_, v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(
    mut v_overlapping_3166_: *mut LeanObject,
    mut v_m_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u64 = 0;
    let mut v___x_3176_: u64 = 0;
    let mut v___x_3177_: u64 = 0;
    let mut v_fold_3178_: u64 = 0;
    let mut v___x_3179_: u64 = 0;
    let mut v___x_3180_: u64 = 0;
    let mut v___x_3181_: u64 = 0;
    let mut v___x_3182_: usize = 0;
    let mut v___x_3183_: usize = 0;
    let mut v___x_3184_: usize = 0;
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v_bkt_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v_val_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3169_ = lean_ctor_get(v_m_3167_, 0);
                v_buckets_3170_ = lean_ctor_get(v_m_3167_, 1);
                v_isSharedCheck_3222_ = (!lean_is_exclusive(v_m_3167_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3172_ = v_m_3167_;
                    v_isShared_3173_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3170_);
                    lean_inc(v_size_3169_);
                    lean_dec(v_m_3167_);
                    v___x_3172_ = lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = lean_array_get_size(v_buckets_3170_);
                v___x_3175_ = lean_uint64_of_nat(v_a_3168_);
                v___x_3176_ = 32u64;
                v___x_3177_ = lean_uint64_shift_right(v___x_3175_, v___x_3176_);
                v_fold_3178_ = lean_uint64_xor(v___x_3175_, v___x_3177_);
                v___x_3179_ = 16u64;
                v___x_3180_ = lean_uint64_shift_right(v_fold_3178_, v___x_3179_);
                v___x_3181_ = lean_uint64_xor(v_fold_3178_, v___x_3180_);
                v___x_3182_ = lean_uint64_to_usize(v___x_3181_);
                v___x_3183_ = lean_usize_of_nat(v___x_3174_);
                v___x_3184_ = 1usize;
                v___x_3185_ = lean_usize_sub(v___x_3183_, v___x_3184_);
                v___x_3186_ = lean_usize_land(v___x_3182_, v___x_3185_);
                v_bkt_3187_ = lean_array_uget_borrowed(v_buckets_3170_, v___x_3186_);
                v___x_3207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3168_, v_bkt_3187_);
                if v___x_3207_ == 0 {
                    v___x_3208_ = lean_box(1);
                    v___x_3209_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_3166_, v___x_3208_);
                    if v___x_3209_ == 0 {
                        v___x_3210_ = lean_box(0);
                        v___x_3211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_3166_, v___x_3210_, v___x_3208_);
                        v___y_3189_ = v___x_3211_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_overlapping_3166_);
                        v___y_3189_ = v___x_3208_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_bkt_3187_);
                    lean_del_object(v___x_3172_);
                    v___x_3212_ = lean_box(0);
                    v_buckets_x27_3213_ =
                        lean_array_uset(v_buckets_3170_, v___x_3186_, v___x_3212_);
                    lean_inc(v_a_3168_);
                    v_bkt_x27_3214_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_3166_, v_a_3168_, v_bkt_3187_);
                    v___x_3219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3168_, v_bkt_x27_3214_);
                    lean_dec(v_a_3168_);
                    if v___x_3219_ == 0 {
                        v___x_3220_ = lean_unsigned_to_nat(1);
                        v___x_3221_ = lean_nat_sub(v_size_3169_, v___x_3220_);
                        lean_dec(v_size_3169_);
                        v___y_3216_ = v___x_3221_;
                        state = 5;
                        continue;
                    } else {
                        v___y_3216_ = v_size_3169_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3190_ = lean_unsigned_to_nat(1);
                v_size_x27_3191_ = lean_nat_add(v_size_3169_, v___x_3190_);
                lean_dec(v_size_3169_);
                lean_inc(v_bkt_3187_);
                v___x_3192_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3192_, 0, v_a_3168_);
                lean_ctor_set(v___x_3192_, 1, v___y_3189_);
                lean_ctor_set(v___x_3192_, 2, v_bkt_3187_);
                v_buckets_x27_3193_ = lean_array_uset(v_buckets_3170_, v___x_3186_, v___x_3192_);
                v___x_3194_ = lean_unsigned_to_nat(4);
                v___x_3195_ = lean_nat_mul(v_size_x27_3191_, v___x_3194_);
                v___x_3196_ = lean_unsigned_to_nat(3);
                v___x_3197_ = lean_nat_div(v___x_3195_, v___x_3196_);
                lean_dec(v___x_3195_);
                v___x_3198_ = lean_array_get_size(v_buckets_x27_3193_);
                v___x_3199_ = lean_nat_dec_le(v___x_3197_, v___x_3198_);
                lean_dec(v___x_3197_);
                if v___x_3199_ == 0 {
                    v_val_3200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_buckets_x27_3193_);
                    if v_isShared_3173_ == 0 {
                        lean_ctor_set(v___x_3172_, 1, v_val_3200_);
                        lean_ctor_set(v___x_3172_, 0, v_size_x27_3191_);
                        v___x_3202_ = v___x_3172_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_size_x27_3191_);
                        lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_val_3200_);
                        v___x_3202_ = v_reuseFailAlloc_3203_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3173_ == 0 {
                        lean_ctor_set(v___x_3172_, 1, v_buckets_x27_3193_);
                        lean_ctor_set(v___x_3172_, 0, v_size_x27_3191_);
                        v___x_3205_ = v___x_3172_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_size_x27_3191_);
                        lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_buckets_x27_3193_);
                        v___x_3205_ = v_reuseFailAlloc_3206_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3202_;
            }
            4 => {
                return v___x_3205_;
            }
            5 => {
                v___x_3217_ = lean_array_uset(v_buckets_x27_3213_, v___x_3186_, v_bkt_x27_3214_);
                v___x_3218_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3218_, 0, v___y_3216_);
                lean_ctor_set(v___x_3218_, 1, v___x_3217_);
                return v___x_3218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_insert(
    mut v_o_3223_: *mut LeanObject,
    mut v_overlapping_3224_: *mut LeanObject,
    mut v_overlapped_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_overlapping_3224_, v_o_3223_, v_overlapped_3225_);
    return v___x_3226_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(
    mut v_00_u03b2_3227_: *mut LeanObject,
    mut v_k_3228_: *mut LeanObject,
    mut v_t_3229_: *mut LeanObject,
) -> u8 {
    let mut v___x_3230_: u8 = 0;
    v___x_3230_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_3228_, v_t_3229_);
    return v___x_3230_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(
    mut v_00_u03b2_3231_: *mut LeanObject,
    mut v_k_3232_: *mut LeanObject,
    mut v_t_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3234_: u8 = 0;
    let mut v_r_3235_: *mut LeanObject = core::ptr::null_mut();
    v_res_3234_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(
            v_00_u03b2_3231_,
            v_k_3232_,
            v_t_3233_,
        );
    lean_dec(v_t_3233_);
    lean_dec(v_k_3232_);
    v_r_3235_ = lean_box((v_res_3234_) as usize);
    return v_r_3235_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(
    mut v_00_u03b2_3236_: *mut LeanObject,
    mut v_k_3237_: *mut LeanObject,
    mut v_v_3238_: *mut LeanObject,
    mut v_t_3239_: *mut LeanObject,
    mut v_hl_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_3237_, v_v_3238_, v_t_3239_);
    return v___x_3241_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(
    mut v_00_u03b2_3242_: *mut LeanObject,
    mut v_a_3243_: *mut LeanObject,
    mut v_x_3244_: *mut LeanObject,
) -> u8 {
    let mut v___x_3245_: u8 = 0;
    v___x_3245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3243_, v_x_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(
    mut v_00_u03b2_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_x_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3249_: u8 = 0;
    let mut v_r_3250_: *mut LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_3246_, v_a_3247_, v_x_3248_);
    lean_dec(v_x_3248_);
    lean_dec(v_a_3247_);
    v_r_3250_ = lean_box((v_res_3249_) as usize);
    return v_r_3250_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(
    mut v_00_u03b2_3251_: *mut LeanObject,
    mut v_data_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_data_3252_);
    return v___x_3253_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3254_: *mut LeanObject,
    mut v_i_3255_: *mut LeanObject,
    mut v_source_3256_: *mut LeanObject,
    mut v_target_3257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    v___x_3258_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v_i_3255_, v_source_3256_, v_target_3257_);
    return v___x_3258_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3259_: *mut LeanObject,
    mut v_x_3260_: *mut LeanObject,
    mut v_x_3261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    v___x_3262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_x_3260_, v_x_3261_);
    return v___x_3262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(
    mut v_a_3263_: *mut LeanObject,
    mut v_x_3264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3264_) == 0 {
                    v___x_3265_ = lean_box(0);
                    return v___x_3265_;
                } else {
                    v_key_3266_ = lean_ctor_get(v_x_3264_, 0);
                    v_value_3267_ = lean_ctor_get(v_x_3264_, 1);
                    v_tail_3268_ = lean_ctor_get(v_x_3264_, 2);
                    v___x_3269_ = lean_nat_dec_eq(v_key_3266_, v_a_3263_);
                    if v___x_3269_ == 0 {
                        v_x_3264_ = v_tail_3268_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3267_);
                        v___x_3271_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3271_, 0, v_value_3267_);
                        return v___x_3271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(
    mut v_a_3272_: *mut LeanObject,
    mut v_x_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3274_: *mut LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_3272_, v_x_3273_);
    lean_dec(v_x_3273_);
    lean_dec(v_a_3272_);
    return v_res_3274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(
    mut v_m_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u64 = 0;
    let mut v___x_3280_: u64 = 0;
    let mut v___x_3281_: u64 = 0;
    let mut v_fold_3282_: u64 = 0;
    let mut v___x_3283_: u64 = 0;
    let mut v___x_3284_: u64 = 0;
    let mut v___x_3285_: u64 = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: usize = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3277_ = lean_ctor_get(v_m_3275_, 1);
    v___x_3278_ = lean_array_get_size(v_buckets_3277_);
    v___x_3279_ = lean_uint64_of_nat(v_a_3276_);
    v___x_3280_ = 32u64;
    v___x_3281_ = lean_uint64_shift_right(v___x_3279_, v___x_3280_);
    v_fold_3282_ = lean_uint64_xor(v___x_3279_, v___x_3281_);
    v___x_3283_ = 16u64;
    v___x_3284_ = lean_uint64_shift_right(v_fold_3282_, v___x_3283_);
    v___x_3285_ = lean_uint64_xor(v_fold_3282_, v___x_3284_);
    v___x_3286_ = lean_uint64_to_usize(v___x_3285_);
    v___x_3287_ = lean_usize_of_nat(v___x_3278_);
    v___x_3288_ = 1usize;
    v___x_3289_ = lean_usize_sub(v___x_3287_, v___x_3288_);
    v___x_3290_ = lean_usize_land(v___x_3286_, v___x_3289_);
    v___x_3291_ = lean_array_uget_borrowed(v_buckets_3277_, v___x_3290_);
    v___x_3292_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_3276_, v___x_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(
    mut v_m_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_3293_, v_a_3294_);
    lean_dec(v_a_3294_);
    lean_dec_ref(v_m_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(
    mut v_init_3296_: *mut LeanObject,
    mut v_x_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3297_) == 0 {
                    v_k_3298_ = lean_ctor_get(v_x_3297_, 1);
                    lean_inc(v_k_3298_);
                    v_l_3299_ = lean_ctor_get(v_x_3297_, 3);
                    lean_inc(v_l_3299_);
                    v_r_3300_ = lean_ctor_get(v_x_3297_, 4);
                    lean_inc(v_r_3300_);
                    lean_dec_ref_known(v_x_3297_, 5);
                    v___x_3301_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_3296_, v_l_3299_);
                    v___x_3302_ = lean_array_push(v___x_3301_, v_k_3298_);
                    v_init_3296_ = v___x_3302_;
                    v_x_3297_ = v_r_3300_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3296_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_overlapping(
    mut v_o_3306_: *mut LeanObject,
    mut v_overlapped_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_3306_, v_overlapped_3307_);
                if lean_obj_tag(v___x_3308_) == 0 {
                    v___x_3309_ = l_Lean_Meta_Match_Overlaps_overlapping___closed__0;
                    return v___x_3309_;
                } else {
                    v_val_3310_ = lean_ctor_get(v___x_3308_, 0);
                    lean_inc(v_val_3310_);
                    lean_dec_ref_known(v___x_3308_, 1);
                    if lean_obj_tag(v_val_3310_) == 0 {
                        v_size_3315_ = lean_ctor_get(v_val_3310_, 0);
                        lean_inc(v_size_3315_);
                        v___y_3312_ = v_size_3315_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3316_ = lean_unsigned_to_nat(0);
                        v___y_3312_ = v___x_3316_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3313_ = lean_mk_empty_array_with_capacity(v___y_3312_);
                lean_dec(v___y_3312_);
                v___x_3314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_3313_, v_val_3310_);
                return v___x_3314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_overlapping___boxed(
    mut v_o_3317_: *mut LeanObject,
    mut v_overlapped_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3319_: *mut LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_3317_, v_overlapped_3318_);
    lean_dec(v_overlapped_3318_);
    lean_dec_ref(v_o_3317_);
    return v_res_3319_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(
    mut v_00_u03b2_3320_: *mut LeanObject,
    mut v_m_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_3321_, v_a_3322_);
    return v___x_3323_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(
    mut v_00_u03b2_3324_: *mut LeanObject,
    mut v_m_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3327_: *mut LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_3324_, v_m_3325_, v_a_3326_);
    lean_dec(v_a_3326_);
    lean_dec_ref(v_m_3325_);
    return v_res_3327_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(
    mut v_init_3328_: *mut LeanObject,
    mut v_t_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_3328_, v_t_3329_);
    return v___x_3330_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(
    mut v_00_u03b2_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_x_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    v___x_3334_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_3332_, v_x_3333_);
    return v___x_3334_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(
    mut v_00_u03b2_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_x_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3338_: *mut LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_3335_, v_a_3336_, v_x_3337_);
    lean_dec(v_x_3337_);
    lean_dec(v_a_3336_);
    return v_res_3338_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    v___x_3353_ = lean_unsigned_to_nat(13);
    v___x_3354_ = lean_nat_to_int(v___x_3353_);
    return v___x_3354_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    v___x_3358_ = lean_unsigned_to_nat(15);
    v___x_3359_ = lean_nat_to_int(v___x_3358_);
    return v___x_3359_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    v___x_3363_ = lean_unsigned_to_nat(16);
    v___x_3364_ = lean_nat_to_int(v___x_3363_);
    return v___x_3364_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(
    mut v_x_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numFields_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3368_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v_numFields_3366_ = lean_ctor_get(v_x_3365_, 0);
    lean_inc(v_numFields_3366_);
    v_numOverlaps_3367_ = lean_ctor_get(v_x_3365_, 1);
    lean_inc(v_numOverlaps_3367_);
    v_hasUnitThunk_3368_ = lean_ctor_get_uint8(
        v_x_3365_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_x_3365_);
    v___x_3369_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5;
    v___x_3370_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3;
    v___x_3371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4,
    );
    v___x_3372_ = l_Nat_reprFast(v_numFields_3366_);
    v___x_3373_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3373_, 0, v___x_3372_);
    v___x_3374_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3374_, 0, v___x_3371_);
    lean_ctor_set(v___x_3374_, 1, v___x_3373_);
    v___x_3375_ = 0;
    v___x_3376_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3376_, 0, v___x_3374_);
    lean_ctor_set_uint8(
        v___x_3376_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3377_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3377_, 0, v___x_3370_);
    lean_ctor_set(v___x_3377_, 1, v___x_3376_);
    v___x_3378_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4;
    v___x_3379_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3379_, 0, v___x_3377_);
    lean_ctor_set(v___x_3379_, 1, v___x_3378_);
    v___x_3380_ = lean_box(1);
    v___x_3381_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3381_, 0, v___x_3379_);
    lean_ctor_set(v___x_3381_, 1, v___x_3380_);
    v___x_3382_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6;
    v___x_3383_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3383_, 0, v___x_3381_);
    lean_ctor_set(v___x_3383_, 1, v___x_3382_);
    v___x_3384_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3384_, 0, v___x_3383_);
    lean_ctor_set(v___x_3384_, 1, v___x_3369_);
    v___x_3385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7,
    );
    v___x_3386_ = l_Nat_reprFast(v_numOverlaps_3367_);
    v___x_3387_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3387_, 0, v___x_3386_);
    v___x_3388_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3388_, 0, v___x_3385_);
    lean_ctor_set(v___x_3388_, 1, v___x_3387_);
    v___x_3389_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3389_, 0, v___x_3388_);
    lean_ctor_set_uint8(
        v___x_3389_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3390_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3390_, 0, v___x_3384_);
    lean_ctor_set(v___x_3390_, 1, v___x_3389_);
    v___x_3391_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3391_, 0, v___x_3390_);
    lean_ctor_set(v___x_3391_, 1, v___x_3378_);
    v___x_3392_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3392_, 0, v___x_3391_);
    lean_ctor_set(v___x_3392_, 1, v___x_3380_);
    v___x_3393_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9;
    v___x_3394_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3394_, 0, v___x_3392_);
    lean_ctor_set(v___x_3394_, 1, v___x_3393_);
    v___x_3395_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3395_, 0, v___x_3394_);
    lean_ctor_set(v___x_3395_, 1, v___x_3369_);
    v___x_3396_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10,
    );
    v___x_3397_ = l_Bool_repr___redArg(v_hasUnitThunk_3368_);
    v___x_3398_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3398_, 0, v___x_3396_);
    lean_ctor_set(v___x_3398_, 1, v___x_3397_);
    v___x_3399_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    lean_ctor_set_uint8(
        v___x_3399_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3400_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3400_, 0, v___x_3395_);
    lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    v___x_3401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_3402_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_3403_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3403_, 0, v___x_3402_);
    lean_ctor_set(v___x_3403_, 1, v___x_3400_);
    v___x_3404_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_3405_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3405_, 0, v___x_3403_);
    lean_ctor_set(v___x_3405_, 1, v___x_3404_);
    v___x_3406_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3406_, 0, v___x_3401_);
    lean_ctor_set(v___x_3406_, 1, v___x_3405_);
    v___x_3407_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3407_, 0, v___x_3406_);
    lean_ctor_set_uint8(
        v___x_3407_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr(
    mut v_x_3408_: *mut LeanObject,
    mut v_prec_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_3408_);
    return v___x_3410_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(
    mut v_x_3411_: *mut LeanObject,
    mut v_prec_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3413_: *mut LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_3411_, v_prec_3412_);
    lean_dec(v_prec_3412_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_Meta_Match_instBEqAltParamInfo_beq(
    mut v_x_3416_: *mut LeanObject,
    mut v_x_3417_: *mut LeanObject,
) -> u8 {
    let mut v_numFields_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3420_: u8 = 0;
    let mut v_numFields_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    v_numFields_3418_ = lean_ctor_get(v_x_3416_, 0);
    v_numOverlaps_3419_ = lean_ctor_get(v_x_3416_, 1);
    v_hasUnitThunk_3420_ = lean_ctor_get_uint8(
        v_x_3416_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_numFields_3421_ = lean_ctor_get(v_x_3417_, 0);
    v_numOverlaps_3422_ = lean_ctor_get(v_x_3417_, 1);
    v_hasUnitThunk_3423_ = lean_ctor_get_uint8(
        v_x_3417_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v___x_3424_ = lean_nat_dec_eq(v_numFields_3418_, v_numFields_3421_);
    if v___x_3424_ == 0 {
        return v___x_3424_;
    } else {
        let mut v___x_3425_: u8 = 0;
        v___x_3425_ = lean_nat_dec_eq(v_numOverlaps_3419_, v_numOverlaps_3422_);
        if v___x_3425_ == 0 {
            return v___x_3425_;
        } else {
            if v_hasUnitThunk_3420_ == 0 {
                if v_hasUnitThunk_3423_ == 0 {
                    return v___x_3425_;
                } else {
                    return v_hasUnitThunk_3420_;
                }
            } else {
                return v_hasUnitThunk_3423_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(
    mut v_x_3426_: *mut LeanObject,
    mut v_x_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3428_: u8 = 0;
    let mut v_r_3429_: *mut LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_3426_, v_x_3427_);
    lean_dec_ref(v_x_3427_);
    lean_dec_ref(v_x_3426_);
    v_r_3429_ = lean_box((v_res_3428_) as usize);
    return v_r_3429_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1()
-> *mut LeanObject {
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
    v___x_3435_ = lean_box(0);
    v___x_3436_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0;
    v___x_3437_ = lean_unsigned_to_nat(0);
    v___x_3438_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3438_, 0, v___x_3437_);
    lean_ctor_set(v___x_3438_, 1, v___x_3437_);
    lean_ctor_set(v___x_3438_, 2, v___x_3436_);
    lean_ctor_set(v___x_3438_, 3, v___x_3435_);
    lean_ctor_set(v___x_3438_, 4, v___x_3436_);
    lean_ctor_set(v___x_3438_, 5, v___x_3434_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default() -> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1,
    );
    return v___x_3439_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo() -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
    return v___x_3440_;
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
    mut v_x_3441_: *mut LeanObject,
    mut v_x_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3441_) == 0 {
                    v___x_3443_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1;
                    return v___x_3443_;
                } else {
                    v_val_3444_ = lean_ctor_get(v_x_3441_, 0);
                    v_isSharedCheck_3455_ = (!lean_is_exclusive(v_x_3441_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3446_ = v_x_3441_;
                        v_isShared_3447_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3444_);
                        lean_dec(v_x_3441_);
                        v___x_3446_ = lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3448_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3;
                v___x_3449_ = l_Nat_reprFast(v_val_3444_);
                if v_isShared_3447_ == 0 {
                    lean_ctor_set_tag(v___x_3446_, 3);
                    lean_ctor_set(v___x_3446_, 0, v___x_3449_);
                    v___x_3451_ = v___x_3446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3449_);
                    v___x_3451_ = v_reuseFailAlloc_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3452_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3452_, 0, v___x_3448_);
                lean_ctor_set(v___x_3452_, 1, v___x_3451_);
                v___x_3453_ = l_Repr_addAppParen(v___x_3452_, v_x_3442_);
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(
    mut v_x_3456_: *mut LeanObject,
    mut v_x_3457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3458_: *mut LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
        v_x_3456_, v_x_3457_,
    );
    lean_dec(v_x_3457_);
    return v_res_3458_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_x_3459_: *mut LeanObject,
    mut v_x_3460_: *mut LeanObject,
    mut v_x_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3461_) == 0 {
                    lean_dec(v_x_3459_);
                    return v_x_3460_;
                } else {
                    v_head_3462_ = lean_ctor_get(v_x_3461_, 0);
                    v_tail_3463_ = lean_ctor_get(v_x_3461_, 1);
                    v_isSharedCheck_3473_ = (!lean_is_exclusive(v_x_3461_)) as u8;
                    if v_isSharedCheck_3473_ == 0 {
                        v___x_3465_ = v_x_3461_;
                        v_isShared_3466_ = v_isSharedCheck_3473_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3463_);
                        lean_inc(v_head_3462_);
                        lean_dec(v_x_3461_);
                        v___x_3465_ = lean_box(0);
                        v_isShared_3466_ = v_isSharedCheck_3473_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3459_);
                if v_isShared_3466_ == 0 {
                    lean_ctor_set_tag(v___x_3465_, 5);
                    lean_ctor_set(v___x_3465_, 1, v_x_3459_);
                    lean_ctor_set(v___x_3465_, 0, v_x_3460_);
                    v___x_3468_ = v___x_3465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_x_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_x_3459_);
                    v___x_3468_ = v_reuseFailAlloc_3472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3469_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3462_);
                v___x_3470_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3470_, 0, v___x_3468_);
                lean_ctor_set(v___x_3470_, 1, v___x_3469_);
                v_x_3460_ = v___x_3470_;
                v_x_3461_ = v_tail_3463_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(
    mut v_x_3474_: *mut LeanObject,
    mut v_x_3475_: *mut LeanObject,
    mut v_x_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3476_) == 0 {
                    lean_dec(v_x_3474_);
                    return v_x_3475_;
                } else {
                    v_head_3477_ = lean_ctor_get(v_x_3476_, 0);
                    v_tail_3478_ = lean_ctor_get(v_x_3476_, 1);
                    v_isSharedCheck_3488_ = (!lean_is_exclusive(v_x_3476_)) as u8;
                    if v_isSharedCheck_3488_ == 0 {
                        v___x_3480_ = v_x_3476_;
                        v_isShared_3481_ = v_isSharedCheck_3488_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3478_);
                        lean_inc(v_head_3477_);
                        lean_dec(v_x_3476_);
                        v___x_3480_ = lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3474_);
                if v_isShared_3481_ == 0 {
                    lean_ctor_set_tag(v___x_3480_, 5);
                    lean_ctor_set(v___x_3480_, 1, v_x_3474_);
                    lean_ctor_set(v___x_3480_, 0, v_x_3475_);
                    v___x_3483_ = v___x_3480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_x_3475_);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_x_3474_);
                    v___x_3483_ = v_reuseFailAlloc_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3477_);
                v___x_3485_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3485_, 0, v___x_3483_);
                lean_ctor_set(v___x_3485_, 1, v___x_3484_);
                v___x_3486_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_3474_, v___x_3485_, v_tail_3478_);
                return v___x_3486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(
    mut v_x_3489_: *mut LeanObject,
    mut v_x_3490_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3489_) == 0 {
        let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3490_);
        v___x_3491_ = lean_box(0);
        return v___x_3491_;
    } else {
        let mut v_tail_3492_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3492_ = lean_ctor_get(v_x_3489_, 1);
        if lean_obj_tag(v_tail_3492_) == 0 {
            let mut v_head_3493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3490_);
            v_head_3493_ = lean_ctor_get(v_x_3489_, 0);
            lean_inc(v_head_3493_);
            lean_dec_ref_known(v_x_3489_, 2);
            v___x_3494_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3493_);
            return v___x_3494_;
        } else {
            let mut v_head_3495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3492_);
            v_head_3495_ = lean_ctor_get(v_x_3489_, 0);
            lean_inc(v_head_3495_);
            lean_dec_ref_known(v_x_3489_, 2);
            v___x_3496_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3495_);
            v___x_3497_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_3490_, v___x_3496_, v_tail_3492_);
            return v___x_3497_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    v___x_3499_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0;
    v___x_3500_ = lean_string_length(v___x_3499_);
    return v___x_3500_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    v___x_3501_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1,
    );
    v___x_3502_ = lean_nat_to_int(v___x_3501_);
    return v___x_3502_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(
    mut v_xs_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    v___x_3509_ = lean_array_get_size(v_xs_3508_);
    v___x_3510_ = lean_unsigned_to_nat(0);
    v___x_3511_ = lean_nat_dec_eq(v___x_3509_, v___x_3510_);
    if v___x_3511_ == 0 {
        let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
        v___x_3512_ = lean_array_to_list(v_xs_3508_);
        v___x_3513_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_3514_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_3512_, v___x_3513_);
        v___x_3515_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
        v___x_3516_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3;
        v___x_3517_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3517_, 0, v___x_3516_);
        lean_ctor_set(v___x_3517_, 1, v___x_3514_);
        v___x_3518_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_3519_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3519_, 0, v___x_3517_);
        lean_ctor_set(v___x_3519_, 1, v___x_3518_);
        v___x_3520_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3520_, 0, v___x_3515_);
        lean_ctor_set(v___x_3520_, 1, v___x_3519_);
        v___x_3521_ = l_Std_Format_fill(v___x_3520_);
        return v___x_3521_;
    } else {
        let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3508_);
        v___x_3522_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5;
        return v___x_3522_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(
    mut v_x_3523_: *mut LeanObject,
    mut v_x_3524_: *mut LeanObject,
    mut v_x_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3530_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3525_) == 0 {
                    lean_dec(v_x_3523_);
                    return v_x_3524_;
                } else {
                    v_head_3526_ = lean_ctor_get(v_x_3525_, 0);
                    v_tail_3527_ = lean_ctor_get(v_x_3525_, 1);
                    v_isSharedCheck_3537_ = (!lean_is_exclusive(v_x_3525_)) as u8;
                    if v_isSharedCheck_3537_ == 0 {
                        v___x_3529_ = v_x_3525_;
                        v_isShared_3530_ = v_isSharedCheck_3537_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3527_);
                        lean_inc(v_head_3526_);
                        lean_dec(v_x_3525_);
                        v___x_3529_ = lean_box(0);
                        v_isShared_3530_ = v_isSharedCheck_3537_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3523_);
                if v_isShared_3530_ == 0 {
                    lean_ctor_set_tag(v___x_3529_, 5);
                    lean_ctor_set(v___x_3529_, 1, v_x_3523_);
                    lean_ctor_set(v___x_3529_, 0, v_x_3524_);
                    v___x_3532_ = v___x_3529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_x_3524_);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_x_3523_);
                    v___x_3532_ = v_reuseFailAlloc_3536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3533_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3526_);
                v___x_3534_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3534_, 0, v___x_3532_);
                lean_ctor_set(v___x_3534_, 1, v___x_3533_);
                v_x_3524_ = v___x_3534_;
                v_x_3525_ = v_tail_3527_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(
    mut v_x_3538_: *mut LeanObject,
    mut v_x_3539_: *mut LeanObject,
    mut v_x_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3540_) == 0 {
                    lean_dec(v_x_3538_);
                    return v_x_3539_;
                } else {
                    v_head_3541_ = lean_ctor_get(v_x_3540_, 0);
                    v_tail_3542_ = lean_ctor_get(v_x_3540_, 1);
                    v_isSharedCheck_3552_ = (!lean_is_exclusive(v_x_3540_)) as u8;
                    if v_isSharedCheck_3552_ == 0 {
                        v___x_3544_ = v_x_3540_;
                        v_isShared_3545_ = v_isSharedCheck_3552_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3542_);
                        lean_inc(v_head_3541_);
                        lean_dec(v_x_3540_);
                        v___x_3544_ = lean_box(0);
                        v_isShared_3545_ = v_isSharedCheck_3552_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3538_);
                if v_isShared_3545_ == 0 {
                    lean_ctor_set_tag(v___x_3544_, 5);
                    lean_ctor_set(v___x_3544_, 1, v_x_3538_);
                    lean_ctor_set(v___x_3544_, 0, v_x_3539_);
                    v___x_3547_ = v___x_3544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3551_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_x_3539_);
                    lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_x_3538_);
                    v___x_3547_ = v_reuseFailAlloc_3551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3548_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3541_);
                v___x_3549_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3549_, 0, v___x_3547_);
                lean_ctor_set(v___x_3549_, 1, v___x_3548_);
                v___x_3550_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_3538_, v___x_3549_, v_tail_3542_);
                return v___x_3550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(
    mut v_x_3553_: *mut LeanObject,
    mut v_x_3554_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3553_) == 0 {
        let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3554_);
        v___x_3555_ = lean_box(0);
        return v___x_3555_;
    } else {
        let mut v_tail_3556_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3556_ = lean_ctor_get(v_x_3553_, 1);
        if lean_obj_tag(v_tail_3556_) == 0 {
            let mut v_head_3557_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3554_);
            v_head_3557_ = lean_ctor_get(v_x_3553_, 0);
            lean_inc(v_head_3557_);
            lean_dec_ref_known(v_x_3553_, 2);
            v___x_3558_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3557_);
            return v___x_3558_;
        } else {
            let mut v_head_3559_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3556_);
            v_head_3559_ = lean_ctor_get(v_x_3553_, 0);
            lean_inc(v_head_3559_);
            lean_dec_ref_known(v_x_3553_, 2);
            v___x_3560_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3559_);
            v___x_3561_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_3554_, v___x_3560_, v_tail_3556_);
            return v___x_3561_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(
    mut v_xs_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    v___x_3563_ = lean_array_get_size(v_xs_3562_);
    v___x_3564_ = lean_unsigned_to_nat(0);
    v___x_3565_ = lean_nat_dec_eq(v___x_3563_, v___x_3564_);
    if v___x_3565_ == 0 {
        let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
        v___x_3566_ = lean_array_to_list(v_xs_3562_);
        v___x_3567_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_3568_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_3566_, v___x_3567_);
        v___x_3569_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
        v___x_3570_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3;
        v___x_3571_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3571_, 0, v___x_3570_);
        lean_ctor_set(v___x_3571_, 1, v___x_3568_);
        v___x_3572_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_3573_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3573_, 0, v___x_3571_);
        lean_ctor_set(v___x_3573_, 1, v___x_3572_);
        v___x_3574_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3574_, 0, v___x_3569_);
        lean_ctor_set(v___x_3574_, 1, v___x_3573_);
        v___x_3575_ = l_Std_Format_fill(v___x_3574_);
        return v___x_3575_;
    } else {
        let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3562_);
        v___x_3576_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5;
        return v___x_3576_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = lean_unsigned_to_nat(12);
    v___x_3593_ = lean_nat_to_int(v___x_3592_);
    return v___x_3593_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v___x_3600_ = lean_unsigned_to_nat(14);
    v___x_3601_ = lean_nat_to_int(v___x_3600_);
    return v___x_3601_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(
    mut v_x_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_altInfos_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uElimPos_x3f_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_overlaps_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_3606_ = lean_ctor_get(v_x_3605_, 0);
    lean_inc(v_numParams_3606_);
    v_numDiscrs_3607_ = lean_ctor_get(v_x_3605_, 1);
    lean_inc(v_numDiscrs_3607_);
    v_altInfos_3608_ = lean_ctor_get(v_x_3605_, 2);
    lean_inc_ref(v_altInfos_3608_);
    v_uElimPos_x3f_3609_ = lean_ctor_get(v_x_3605_, 3);
    lean_inc(v_uElimPos_x3f_3609_);
    v_discrInfos_3610_ = lean_ctor_get(v_x_3605_, 4);
    lean_inc_ref(v_discrInfos_3610_);
    v_overlaps_3611_ = lean_ctor_get(v_x_3605_, 5);
    lean_inc_ref(v_overlaps_3611_);
    lean_dec_ref(v_x_3605_);
    v___x_3612_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5;
    v___x_3613_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3;
    v___x_3614_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4,
    );
    v___x_3615_ = l_Nat_reprFast(v_numParams_3606_);
    v___x_3616_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3616_, 0, v___x_3615_);
    v___x_3617_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3617_, 0, v___x_3614_);
    lean_ctor_set(v___x_3617_, 1, v___x_3616_);
    v___x_3618_ = 0;
    v___x_3619_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3619_, 0, v___x_3617_);
    lean_ctor_set_uint8(
        v___x_3619_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3620_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3620_, 0, v___x_3613_);
    lean_ctor_set(v___x_3620_, 1, v___x_3619_);
    v___x_3621_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4;
    v___x_3622_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3622_, 0, v___x_3620_);
    lean_ctor_set(v___x_3622_, 1, v___x_3621_);
    v___x_3623_ = lean_box(1);
    v___x_3624_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3624_, 0, v___x_3622_);
    lean_ctor_set(v___x_3624_, 1, v___x_3623_);
    v___x_3625_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5;
    v___x_3626_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3626_, 0, v___x_3624_);
    lean_ctor_set(v___x_3626_, 1, v___x_3625_);
    v___x_3627_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3627_, 0, v___x_3626_);
    lean_ctor_set(v___x_3627_, 1, v___x_3612_);
    v___x_3628_ = l_Nat_reprFast(v_numDiscrs_3607_);
    v___x_3629_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3629_, 0, v___x_3628_);
    v___x_3630_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3630_, 0, v___x_3614_);
    lean_ctor_set(v___x_3630_, 1, v___x_3629_);
    v___x_3631_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3631_, 0, v___x_3630_);
    lean_ctor_set_uint8(
        v___x_3631_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3632_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3632_, 0, v___x_3627_);
    lean_ctor_set(v___x_3632_, 1, v___x_3631_);
    v___x_3633_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3633_, 0, v___x_3632_);
    lean_ctor_set(v___x_3633_, 1, v___x_3621_);
    v___x_3634_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3634_, 0, v___x_3633_);
    lean_ctor_set(v___x_3634_, 1, v___x_3623_);
    v___x_3635_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7;
    v___x_3636_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3636_, 0, v___x_3634_);
    lean_ctor_set(v___x_3636_, 1, v___x_3635_);
    v___x_3637_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3637_, 0, v___x_3636_);
    lean_ctor_set(v___x_3637_, 1, v___x_3612_);
    v___x_3638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once
        ),
        _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8,
    );
    v___x_3639_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_3608_);
    v___x_3640_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3640_, 0, v___x_3638_);
    lean_ctor_set(v___x_3640_, 1, v___x_3639_);
    v___x_3641_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3641_, 0, v___x_3640_);
    lean_ctor_set_uint8(
        v___x_3641_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3642_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3642_, 0, v___x_3637_);
    lean_ctor_set(v___x_3642_, 1, v___x_3641_);
    v___x_3643_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3643_, 0, v___x_3642_);
    lean_ctor_set(v___x_3643_, 1, v___x_3621_);
    v___x_3644_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3644_, 0, v___x_3643_);
    lean_ctor_set(v___x_3644_, 1, v___x_3623_);
    v___x_3645_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10;
    v___x_3646_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3646_, 0, v___x_3644_);
    lean_ctor_set(v___x_3646_, 1, v___x_3645_);
    v___x_3647_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3647_, 0, v___x_3646_);
    lean_ctor_set(v___x_3647_, 1, v___x_3612_);
    v___x_3648_ = lean_unsigned_to_nat(0);
    v___x_3649_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
        v_uElimPos_x3f_3609_,
        v___x_3648_,
    );
    v___x_3650_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3650_, 0, v___x_3614_);
    lean_ctor_set(v___x_3650_, 1, v___x_3649_);
    v___x_3651_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3651_, 0, v___x_3650_);
    lean_ctor_set_uint8(
        v___x_3651_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3652_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3652_, 0, v___x_3647_);
    lean_ctor_set(v___x_3652_, 1, v___x_3651_);
    v___x_3653_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3653_, 0, v___x_3652_);
    lean_ctor_set(v___x_3653_, 1, v___x_3621_);
    v___x_3654_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3654_, 0, v___x_3653_);
    lean_ctor_set(v___x_3654_, 1, v___x_3623_);
    v___x_3655_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12;
    v___x_3656_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3656_, 0, v___x_3654_);
    lean_ctor_set(v___x_3656_, 1, v___x_3655_);
    v___x_3657_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3657_, 0, v___x_3656_);
    lean_ctor_set(v___x_3657_, 1, v___x_3612_);
    v___x_3658_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13,
    );
    v___x_3659_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_3610_);
    v___x_3660_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3660_, 0, v___x_3658_);
    lean_ctor_set(v___x_3660_, 1, v___x_3659_);
    v___x_3661_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3661_, 0, v___x_3660_);
    lean_ctor_set_uint8(
        v___x_3661_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3662_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3662_, 0, v___x_3657_);
    lean_ctor_set(v___x_3662_, 1, v___x_3661_);
    v___x_3663_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3663_, 0, v___x_3662_);
    lean_ctor_set(v___x_3663_, 1, v___x_3621_);
    v___x_3664_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    lean_ctor_set(v___x_3664_, 1, v___x_3623_);
    v___x_3665_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15;
    v___x_3666_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3666_, 0, v___x_3664_);
    lean_ctor_set(v___x_3666_, 1, v___x_3665_);
    v___x_3667_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    lean_ctor_set(v___x_3667_, 1, v___x_3612_);
    v___x_3668_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_3611_);
    v___x_3669_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3669_, 0, v___x_3638_);
    lean_ctor_set(v___x_3669_, 1, v___x_3668_);
    v___x_3670_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3670_, 0, v___x_3669_);
    lean_ctor_set_uint8(
        v___x_3670_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3671_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3671_, 0, v___x_3667_);
    lean_ctor_set(v___x_3671_, 1, v___x_3670_);
    v___x_3672_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_3673_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_3674_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3674_, 0, v___x_3673_);
    lean_ctor_set(v___x_3674_, 1, v___x_3671_);
    v___x_3675_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_3676_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3676_, 0, v___x_3674_);
    lean_ctor_set(v___x_3676_, 1, v___x_3675_);
    v___x_3677_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3677_, 0, v___x_3672_);
    lean_ctor_set(v___x_3677_, 1, v___x_3676_);
    v___x_3678_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    return v___x_3678_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr(
    mut v_x_3679_: *mut LeanObject,
    mut v_prec_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_3679_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(
    mut v_x_3682_: *mut LeanObject,
    mut v_prec_3683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3684_: *mut LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_3682_, v_prec_3683_);
    lean_dec(v_prec_3683_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_numAlts(
    mut v_info_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_altInfos_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v_altInfos_3688_ = lean_ctor_get(v_info_3687_, 2);
    v___x_3689_ = lean_array_get_size(v_altInfos_3688_);
    return v___x_3689_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(
    mut v_info_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3691_: *mut LeanObject = core::ptr::null_mut();
    v_res_3691_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3690_);
    lean_dec_ref(v_info_3690_);
    return v_res_3691_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_arity(
    mut v_info_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_3693_ = lean_ctor_get(v_info_3692_, 0);
    v_numDiscrs_3694_ = lean_ctor_get(v_info_3692_, 1);
    v___x_3695_ = lean_unsigned_to_nat(1);
    v___x_3696_ = lean_nat_add(v_numParams_3693_, v___x_3695_);
    v___x_3697_ = lean_nat_add(v___x_3696_, v_numDiscrs_3694_);
    lean_dec(v___x_3696_);
    v___x_3698_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3692_);
    v___x_3699_ = lean_nat_add(v___x_3697_, v___x_3698_);
    lean_dec(v___x_3698_);
    lean_dec(v___x_3697_);
    return v___x_3699_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_arity___boxed(
    mut v_info_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3701_: *mut LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_3700_);
    lean_dec_ref(v_info_3700_);
    return v_res_3701_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(
    mut v_info_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_3703_ = lean_ctor_get(v_info_3702_, 0);
    v___x_3704_ = lean_unsigned_to_nat(1);
    v___x_3705_ = lean_nat_add(v_numParams_3703_, v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(
    mut v_info_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3707_: *mut LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_3706_);
    lean_dec_ref(v_info_3706_);
    return v_res_3707_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getDiscrRange(
    mut v_info_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numDiscrs_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v_numDiscrs_3709_ = lean_ctor_get(v_info_3708_, 1);
    v___x_3710_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_3708_);
    v___x_3711_ = lean_nat_add(v___x_3710_, v_numDiscrs_3709_);
    v___x_3712_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3712_, 0, v___x_3710_);
    lean_ctor_set(v___x_3712_, 1, v___x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(
    mut v_info_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3714_: *mut LeanObject = core::ptr::null_mut();
    v_res_3714_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_3713_);
    lean_dec_ref(v_info_3713_);
    return v_res_3714_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(
    mut v_info_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_3716_ = lean_ctor_get(v_info_3715_, 0);
    v_numDiscrs_3717_ = lean_ctor_get(v_info_3715_, 1);
    v___x_3718_ = lean_unsigned_to_nat(1);
    v___x_3719_ = lean_nat_add(v_numParams_3716_, v___x_3718_);
    v___x_3720_ = lean_nat_add(v___x_3719_, v_numDiscrs_3717_);
    lean_dec(v___x_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(
    mut v_info_3721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3722_: *mut LeanObject = core::ptr::null_mut();
    v_res_3722_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_3721_);
    lean_dec_ref(v_info_3721_);
    return v_res_3722_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getAltRange(
    mut v_info_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_3723_);
    v___x_3725_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3723_);
    v___x_3726_ = lean_nat_add(v___x_3724_, v___x_3725_);
    lean_dec(v___x_3725_);
    v___x_3727_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3727_, 0, v___x_3724_);
    lean_ctor_set(v___x_3727_, 1, v___x_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(
    mut v_info_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3729_: *mut LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_3728_);
    lean_dec_ref(v_info_3728_);
    return v_res_3729_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getMotivePos(
    mut v_info_3730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3731_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_3731_ = lean_ctor_get(v_info_3730_, 0);
    lean_inc(v_numParams_3731_);
    return v_numParams_3731_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(
    mut v_info_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3733_: *mut LeanObject = core::ptr::null_mut();
    v_res_3733_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_3732_);
    lean_dec_ref(v_info_3732_);
    return v_res_3733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(
    mut v_as_3734_: *mut LeanObject,
    mut v_sz_3735_: usize,
    mut v_i_3736_: usize,
    mut v_b_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: usize = 0;
    let mut v___x_3741_: usize = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v_a_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3743_ = lean_usize_dec_lt(v_i_3736_, v_sz_3735_);
                if v___x_3743_ == 0 {
                    return v_b_3737_;
                } else {
                    v_a_3744_ = lean_array_uget_borrowed(v_as_3734_, v_i_3736_);
                    if lean_obj_tag(v_a_3744_) == 0 {
                        v_a_3739_ = v_b_3737_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3745_ = lean_unsigned_to_nat(1);
                        v___x_3746_ = lean_nat_add(v_b_3737_, v___x_3745_);
                        lean_dec(v_b_3737_);
                        v_a_3739_ = v___x_3746_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3740_ = 1usize;
                v___x_3741_ = lean_usize_add(v_i_3736_, v___x_3740_);
                v_i_3736_ = v___x_3741_;
                v_b_3737_ = v_a_3739_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(
    mut v_as_3747_: *mut LeanObject,
    mut v_sz_3748_: *mut LeanObject,
    mut v_i_3749_: *mut LeanObject,
    mut v_b_3750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3751_: usize = 0;
    let mut v_i_boxed_3752_: usize = 0;
    let mut v_res_3753_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3751_ = lean_unbox_usize(v_sz_3748_);
    lean_dec(v_sz_3748_);
    v_i_boxed_3752_ = lean_unbox_usize(v_i_3749_);
    lean_dec(v_i_3749_);
    v_res_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_3747_, v_sz_boxed_3751_, v_i_boxed_3752_, v_b_3750_);
    lean_dec_ref(v_as_3747_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Meta_Match_getNumEqsFromDiscrInfos(
    mut v_infos_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3756_: usize = 0;
    let mut v___x_3757_: usize = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v_r_3755_ = lean_unsigned_to_nat(0);
    v_sz_3756_ = lean_array_size(v_infos_3754_);
    v___x_3757_ = 0usize;
    v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_3754_, v_sz_3756_, v___x_3757_, v_r_3755_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(
    mut v_infos_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3760_: *mut LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_3759_);
    lean_dec_ref(v_infos_3759_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(
    mut v_info_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_discrInfos_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    v_discrInfos_3762_ = lean_ctor_get(v_info_3761_, 4);
    v___x_3763_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3762_);
    return v___x_3763_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(
    mut v_info_3764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3765_: *mut LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_3764_);
    lean_dec_ref(v_info_3764_);
    return v_res_3765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(
    mut v_info_3766_: *mut LeanObject,
    mut v_sz_3767_: usize,
    mut v_i_3768_: usize,
    mut v_bs_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3770_: u8 = 0;
    let mut v_v_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3774_: u8 = 0;
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: usize = 0;
    let mut v___x_3784_: usize = 0;
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = lean_usize_dec_lt(v_i_3768_, v_sz_3767_);
                if v___x_3770_ == 0 {
                    return v_bs_3769_;
                } else {
                    v_v_3771_ = lean_array_uget_borrowed(v_bs_3769_, v_i_3768_);
                    v_numFields_3772_ = lean_ctor_get(v_v_3771_, 0);
                    lean_inc(v_numFields_3772_);
                    v_numOverlaps_3773_ = lean_ctor_get(v_v_3771_, 1);
                    lean_inc(v_numOverlaps_3773_);
                    v_hasUnitThunk_3774_ = lean_ctor_get_uint8(
                        v_v_3771_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_3775_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3776_ = lean_array_uset(v_bs_3769_, v_i_3768_, v___x_3775_);
                    v___x_3777_ = lean_nat_add(v_numFields_3772_, v_numOverlaps_3773_);
                    lean_dec(v_numOverlaps_3773_);
                    lean_dec(v_numFields_3772_);
                    if v_hasUnitThunk_3774_ == 0 {
                        v___y_3779_ = v___x_3775_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3787_ = lean_unsigned_to_nat(1);
                        v___y_3779_ = v___x_3787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3780_ = lean_nat_add(v___x_3777_, v___y_3779_);
                lean_dec(v___y_3779_);
                lean_dec(v___x_3777_);
                v___x_3781_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_3766_);
                v___x_3782_ = lean_nat_add(v___x_3780_, v___x_3781_);
                lean_dec(v___x_3781_);
                lean_dec(v___x_3780_);
                v___x_3783_ = 1usize;
                v___x_3784_ = lean_usize_add(v_i_3768_, v___x_3783_);
                v___x_3785_ = lean_array_uset(v_bs_x27_3776_, v_i_3768_, v___x_3782_);
                v_i_3768_ = v___x_3784_;
                v_bs_3769_ = v___x_3785_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(
    mut v_info_3788_: *mut LeanObject,
    mut v_sz_3789_: *mut LeanObject,
    mut v_i_3790_: *mut LeanObject,
    mut v_bs_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3792_: usize = 0;
    let mut v_i_boxed_3793_: usize = 0;
    let mut v_res_3794_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3789_);
    lean_dec(v_sz_3789_);
    v_i_boxed_3793_ = lean_unbox_usize(v_i_3790_);
    lean_dec(v_i_3790_);
    v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_3788_, v_sz_boxed_3792_, v_i_boxed_3793_, v_bs_3791_);
    lean_dec_ref(v_info_3788_);
    return v_res_3794_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_altNumParams(
    mut v_info_3795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_altInfos_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3797_: usize = 0;
    let mut v___x_3798_: usize = 0;
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    v_altInfos_3796_ = lean_ctor_get(v_info_3795_, 2);
    lean_inc_ref(v_altInfos_3796_);
    v_sz_3797_ = lean_array_size(v_altInfos_3796_);
    v___x_3798_ = 0usize;
    v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_3795_, v_sz_3797_, v___x_3798_, v_altInfos_3796_);
    lean_dec_ref(v_info_3795_);
    return v___x_3799_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0() -> *mut LeanObject
{
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3800_ = lean_box(0);
    v___x_3801_ = lean_unsigned_to_nat(16);
    v___x_3802_ = lean_mk_array(v___x_3801_, v___x_3800_);
    return v___x_3802_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1() -> *mut LeanObject
{
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    v___x_3803_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0,
    );
    v___x_3804_ = lean_unsigned_to_nat(0);
    v___x_3805_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3805_, 0, v___x_3804_);
    lean_ctor_set(v___x_3805_, 1, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2() -> *mut LeanObject
{
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    v___x_3806_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3806_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3() -> *mut LeanObject
{
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    v___x_3807_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2,
    );
    v___x_3808_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3808_, 0, v___x_3807_);
    return v___x_3808_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4() -> *mut LeanObject
{
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v___x_3809_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3,
    );
    v___x_3810_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1,
    );
    v___x_3811_ = 1;
    v___x_3812_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_3812_, 0, v___x_3810_);
    lean_ctor_set(v___x_3812_, 1, v___x_3809_);
    lean_ctor_set_uint8(
        v___x_3812_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_3811_,
    );
    return v___x_3812_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState() -> *mut LeanObject {
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4,
    );
    return v___x_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(
    mut v_a_3814_: *mut LeanObject,
    mut v_x_3815_: *mut LeanObject,
) -> u8 {
    let mut v___x_3816_: u8 = 0;
    let mut v_key_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3815_) == 0 {
                    v___x_3816_ = 0;
                    return v___x_3816_;
                } else {
                    v_key_3817_ = lean_ctor_get(v_x_3815_, 0);
                    v_tail_3818_ = lean_ctor_get(v_x_3815_, 2);
                    v___x_3819_ = lean_name_eq(v_key_3817_, v_a_3814_);
                    if v___x_3819_ == 0 {
                        v_x_3815_ = v_tail_3818_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3819_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3821_: *mut LeanObject,
    mut v_x_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3823_: u8 = 0;
    let mut v_r_3824_: *mut LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_3821_, v_x_3822_);
    lean_dec(v_x_3822_);
    lean_dec(v_a_3821_);
    v_r_3824_ = lean_box((v_res_3823_) as usize);
    return v_r_3824_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0()
-> u64 {
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u64 = 0;
    v___x_3825_ = lean_unsigned_to_nat(1723);
    v___x_3826_ = lean_uint64_of_nat(v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_3827_: *mut LeanObject,
    mut v_x_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3834_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: u64 = 0;
    let mut v___x_3838_: u64 = 0;
    let mut v___x_3839_: u64 = 0;
    let mut v_fold_3840_: u64 = 0;
    let mut v___x_3841_: u64 = 0;
    let mut v___x_3842_: u64 = 0;
    let mut v___x_3843_: u64 = 0;
    let mut v___x_3844_: usize = 0;
    let mut v___x_3845_: usize = 0;
    let mut v___x_3846_: usize = 0;
    let mut v___x_3847_: usize = 0;
    let mut v___x_3848_: usize = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u64 = 0;
    let mut v_hash_3856_: u64 = 0;
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3828_) == 0 {
                    return v_x_3827_;
                } else {
                    v_key_3829_ = lean_ctor_get(v_x_3828_, 0);
                    v_value_3830_ = lean_ctor_get(v_x_3828_, 1);
                    v_tail_3831_ = lean_ctor_get(v_x_3828_, 2);
                    v_isSharedCheck_3857_ = (!lean_is_exclusive(v_x_3828_)) as u8;
                    if v_isSharedCheck_3857_ == 0 {
                        v___x_3833_ = v_x_3828_;
                        v_isShared_3834_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3831_);
                        lean_inc(v_value_3830_);
                        lean_inc(v_key_3829_);
                        lean_dec(v_x_3828_);
                        v___x_3833_ = lean_box(0);
                        v_isShared_3834_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3835_ = lean_array_get_size(v_x_3827_);
                if lean_obj_tag(v_key_3829_) == 0 {
                    v___x_3855_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_3837_ = v___x_3855_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3856_ = lean_ctor_get_uint64(
                        v_key_3829_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3837_ = v_hash_3856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3838_ = 32u64;
                v___x_3839_ = lean_uint64_shift_right(v___y_3837_, v___x_3838_);
                v_fold_3840_ = lean_uint64_xor(v___y_3837_, v___x_3839_);
                v___x_3841_ = 16u64;
                v___x_3842_ = lean_uint64_shift_right(v_fold_3840_, v___x_3841_);
                v___x_3843_ = lean_uint64_xor(v_fold_3840_, v___x_3842_);
                v___x_3844_ = lean_uint64_to_usize(v___x_3843_);
                v___x_3845_ = lean_usize_of_nat(v___x_3835_);
                v___x_3846_ = 1usize;
                v___x_3847_ = lean_usize_sub(v___x_3845_, v___x_3846_);
                v___x_3848_ = lean_usize_land(v___x_3844_, v___x_3847_);
                v___x_3849_ = lean_array_uget_borrowed(v_x_3827_, v___x_3848_);
                lean_inc(v___x_3849_);
                if v_isShared_3834_ == 0 {
                    lean_ctor_set(v___x_3833_, 2, v___x_3849_);
                    v___x_3851_ = v___x_3833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_key_3829_);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_value_3830_);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 2, v___x_3849_);
                    v___x_3851_ = v_reuseFailAlloc_3854_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3852_ = lean_array_uset(v_x_3827_, v___x_3848_, v___x_3851_);
                v_x_3827_ = v___x_3852_;
                v_x_3828_ = v_tail_3831_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_3858_: *mut LeanObject,
    mut v_source_3859_: *mut LeanObject,
    mut v_target_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v_es_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = lean_array_get_size(v_source_3859_);
                v___x_3862_ = lean_nat_dec_lt(v_i_3858_, v___x_3861_);
                if v___x_3862_ == 0 {
                    lean_dec_ref(v_source_3859_);
                    lean_dec(v_i_3858_);
                    return v_target_3860_;
                } else {
                    v_es_3863_ = lean_array_fget(v_source_3859_, v_i_3858_);
                    v___x_3864_ = lean_box(0);
                    v_source_3865_ = lean_array_fset(v_source_3859_, v_i_3858_, v___x_3864_);
                    v_target_3866_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_3860_, v_es_3863_);
                    v___x_3867_ = lean_unsigned_to_nat(1);
                    v___x_3868_ = lean_nat_add(v_i_3858_, v___x_3867_);
                    lean_dec(v_i_3858_);
                    v_i_3858_ = v___x_3868_;
                    v_source_3859_ = v_source_3865_;
                    v_target_3860_ = v_target_3866_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(
    mut v_data_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    v___x_3871_ = lean_array_get_size(v_data_3870_);
    v___x_3872_ = lean_unsigned_to_nat(2);
    v_nbuckets_3873_ = lean_nat_mul(v___x_3871_, v___x_3872_);
    v___x_3874_ = lean_unsigned_to_nat(0);
    v___x_3875_ = lean_box(0);
    v___x_3876_ = lean_mk_array(v_nbuckets_3873_, v___x_3875_);
    v___x_3877_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_3874_, v_data_3870_, v___x_3876_);
    return v___x_3877_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(
    mut v_a_3878_: *mut LeanObject,
    mut v_b_3879_: *mut LeanObject,
    mut v_x_3880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3880_) == 0 {
                    lean_dec(v_b_3879_);
                    lean_dec(v_a_3878_);
                    return v_x_3880_;
                } else {
                    v_key_3881_ = lean_ctor_get(v_x_3880_, 0);
                    v_value_3882_ = lean_ctor_get(v_x_3880_, 1);
                    v_tail_3883_ = lean_ctor_get(v_x_3880_, 2);
                    v_isSharedCheck_3895_ = (!lean_is_exclusive(v_x_3880_)) as u8;
                    if v_isSharedCheck_3895_ == 0 {
                        v___x_3885_ = v_x_3880_;
                        v_isShared_3886_ = v_isSharedCheck_3895_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3883_);
                        lean_inc(v_value_3882_);
                        lean_inc(v_key_3881_);
                        lean_dec(v_x_3880_);
                        v___x_3885_ = lean_box(0);
                        v_isShared_3886_ = v_isSharedCheck_3895_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3887_ = lean_name_eq(v_key_3881_, v_a_3878_);
                if v___x_3887_ == 0 {
                    v___x_3888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_3878_, v_b_3879_, v_tail_3883_);
                    if v_isShared_3886_ == 0 {
                        lean_ctor_set(v___x_3885_, 2, v___x_3888_);
                        v___x_3890_ = v___x_3885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_key_3881_);
                        lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_value_3882_);
                        lean_ctor_set(v_reuseFailAlloc_3891_, 2, v___x_3888_);
                        v___x_3890_ = v_reuseFailAlloc_3891_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3882_);
                    lean_dec(v_key_3881_);
                    if v_isShared_3886_ == 0 {
                        lean_ctor_set(v___x_3885_, 1, v_b_3879_);
                        lean_ctor_set(v___x_3885_, 0, v_a_3878_);
                        v___x_3893_ = v___x_3885_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3878_);
                        lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_b_3879_);
                        lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_tail_3883_);
                        v___x_3893_ = v_reuseFailAlloc_3894_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3890_;
            }
            3 => {
                return v___x_3893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(
    mut v_m_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_b_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: u64 = 0;
    let mut v___x_3907_: u64 = 0;
    let mut v___x_3908_: u64 = 0;
    let mut v_fold_3909_: u64 = 0;
    let mut v___x_3910_: u64 = 0;
    let mut v___x_3911_: u64 = 0;
    let mut v___x_3912_: u64 = 0;
    let mut v___x_3913_: usize = 0;
    let mut v___x_3914_: usize = 0;
    let mut v___x_3915_: usize = 0;
    let mut v___x_3916_: usize = 0;
    let mut v___x_3917_: usize = 0;
    let mut v_bkt_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: u8 = 0;
    let mut v_val_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u64 = 0;
    let mut v_hash_3945_: u64 = 0;
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3899_ = lean_ctor_get(v_m_3896_, 0);
                v_buckets_3900_ = lean_ctor_get(v_m_3896_, 1);
                v_isSharedCheck_3946_ = (!lean_is_exclusive(v_m_3896_)) as u8;
                if v_isSharedCheck_3946_ == 0 {
                    v___x_3902_ = v_m_3896_;
                    v_isShared_3903_ = v_isSharedCheck_3946_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3900_);
                    lean_inc(v_size_3899_);
                    lean_dec(v_m_3896_);
                    v___x_3902_ = lean_box(0);
                    v_isShared_3903_ = v_isSharedCheck_3946_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3904_ = lean_array_get_size(v_buckets_3900_);
                if lean_obj_tag(v_a_3897_) == 0 {
                    v___x_3944_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_3906_ = v___x_3944_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3945_ = lean_ctor_get_uint64(
                        v_a_3897_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3906_ = v_hash_3945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3907_ = 32u64;
                v___x_3908_ = lean_uint64_shift_right(v___y_3906_, v___x_3907_);
                v_fold_3909_ = lean_uint64_xor(v___y_3906_, v___x_3908_);
                v___x_3910_ = 16u64;
                v___x_3911_ = lean_uint64_shift_right(v_fold_3909_, v___x_3910_);
                v___x_3912_ = lean_uint64_xor(v_fold_3909_, v___x_3911_);
                v___x_3913_ = lean_uint64_to_usize(v___x_3912_);
                v___x_3914_ = lean_usize_of_nat(v___x_3904_);
                v___x_3915_ = 1usize;
                v___x_3916_ = lean_usize_sub(v___x_3914_, v___x_3915_);
                v___x_3917_ = lean_usize_land(v___x_3913_, v___x_3916_);
                v_bkt_3918_ = lean_array_uget_borrowed(v_buckets_3900_, v___x_3917_);
                v___x_3919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_3897_, v_bkt_3918_);
                if v___x_3919_ == 0 {
                    v___x_3920_ = lean_unsigned_to_nat(1);
                    v_size_x27_3921_ = lean_nat_add(v_size_3899_, v___x_3920_);
                    lean_dec(v_size_3899_);
                    lean_inc(v_bkt_3918_);
                    v___x_3922_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3922_, 0, v_a_3897_);
                    lean_ctor_set(v___x_3922_, 1, v_b_3898_);
                    lean_ctor_set(v___x_3922_, 2, v_bkt_3918_);
                    v_buckets_x27_3923_ =
                        lean_array_uset(v_buckets_3900_, v___x_3917_, v___x_3922_);
                    v___x_3924_ = lean_unsigned_to_nat(4);
                    v___x_3925_ = lean_nat_mul(v_size_x27_3921_, v___x_3924_);
                    v___x_3926_ = lean_unsigned_to_nat(3);
                    v___x_3927_ = lean_nat_div(v___x_3925_, v___x_3926_);
                    lean_dec(v___x_3925_);
                    v___x_3928_ = lean_array_get_size(v_buckets_x27_3923_);
                    v___x_3929_ = lean_nat_dec_le(v___x_3927_, v___x_3928_);
                    lean_dec(v___x_3927_);
                    if v___x_3929_ == 0 {
                        v_val_3930_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_3923_);
                        if v_isShared_3903_ == 0 {
                            lean_ctor_set(v___x_3902_, 1, v_val_3930_);
                            lean_ctor_set(v___x_3902_, 0, v_size_x27_3921_);
                            v___x_3932_ = v___x_3902_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_size_x27_3921_);
                            lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_val_3930_);
                            v___x_3932_ = v_reuseFailAlloc_3933_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3903_ == 0 {
                            lean_ctor_set(v___x_3902_, 1, v_buckets_x27_3923_);
                            lean_ctor_set(v___x_3902_, 0, v_size_x27_3921_);
                            v___x_3935_ = v___x_3902_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_size_x27_3921_);
                            lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_buckets_x27_3923_);
                            v___x_3935_ = v_reuseFailAlloc_3936_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3918_);
                    v___x_3937_ = lean_box(0);
                    v_buckets_x27_3938_ =
                        lean_array_uset(v_buckets_3900_, v___x_3917_, v___x_3937_);
                    v___x_3939_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_3897_, v_b_3898_, v_bkt_3918_);
                    v___x_3940_ = lean_array_uset(v_buckets_x27_3938_, v___x_3917_, v___x_3939_);
                    if v_isShared_3903_ == 0 {
                        lean_ctor_set(v___x_3902_, 1, v___x_3940_);
                        v___x_3942_ = v___x_3902_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_size_3899_);
                        lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3940_);
                        v___x_3942_ = v_reuseFailAlloc_3943_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3932_;
            }
            4 => {
                return v___x_3935_;
            }
            5 => {
                return v___x_3942_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_3947_: *mut LeanObject,
    mut v_x_3948_: *mut LeanObject,
    mut v_x_3949_: *mut LeanObject,
    mut v_x_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3951_ = lean_ctor_get(v_x_3947_, 0);
                v_vs_3952_ = lean_ctor_get(v_x_3947_, 1);
                v_isSharedCheck_3976_ = (!lean_is_exclusive(v_x_3947_)) as u8;
                if v_isSharedCheck_3976_ == 0 {
                    v___x_3954_ = v_x_3947_;
                    v_isShared_3955_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3952_);
                    lean_inc(v_ks_3951_);
                    lean_dec(v_x_3947_);
                    v___x_3954_ = lean_box(0);
                    v_isShared_3955_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3956_ = lean_array_get_size(v_ks_3951_);
                v___x_3957_ = lean_nat_dec_lt(v_x_3948_, v___x_3956_);
                if v___x_3957_ == 0 {
                    lean_dec(v_x_3948_);
                    v___x_3958_ = lean_array_push(v_ks_3951_, v_x_3949_);
                    v___x_3959_ = lean_array_push(v_vs_3952_, v_x_3950_);
                    if v_isShared_3955_ == 0 {
                        lean_ctor_set(v___x_3954_, 1, v___x_3959_);
                        lean_ctor_set(v___x_3954_, 0, v___x_3958_);
                        v___x_3961_ = v___x_3954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3958_);
                        lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3959_);
                        v___x_3961_ = v_reuseFailAlloc_3962_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3963_ = lean_array_fget_borrowed(v_ks_3951_, v_x_3948_);
                    v___x_3964_ = lean_name_eq(v_x_3949_, v_k_x27_3963_);
                    if v___x_3964_ == 0 {
                        if v_isShared_3955_ == 0 {
                            v___x_3966_ = v___x_3954_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_ks_3951_);
                            lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_vs_3952_);
                            v___x_3966_ = v_reuseFailAlloc_3970_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3971_ = lean_array_fset(v_ks_3951_, v_x_3948_, v_x_3949_);
                        v___x_3972_ = lean_array_fset(v_vs_3952_, v_x_3948_, v_x_3950_);
                        lean_dec(v_x_3948_);
                        if v_isShared_3955_ == 0 {
                            lean_ctor_set(v___x_3954_, 1, v___x_3972_);
                            lean_ctor_set(v___x_3954_, 0, v___x_3971_);
                            v___x_3974_ = v___x_3954_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3971_);
                            lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3972_);
                            v___x_3974_ = v_reuseFailAlloc_3975_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3961_;
            }
            3 => {
                v___x_3967_ = lean_unsigned_to_nat(1);
                v___x_3968_ = lean_nat_add(v_x_3948_, v___x_3967_);
                lean_dec(v_x_3948_);
                v_x_3947_ = v___x_3966_;
                v_x_3948_ = v___x_3968_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_3977_: *mut LeanObject,
    mut v_k_3978_: *mut LeanObject,
    mut v_v_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    v___x_3980_ = lean_unsigned_to_nat(0);
    v___x_3981_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_3977_, v___x_3980_, v_k_3978_, v_v_3979_);
    return v___x_3981_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: usize = 0;
    let mut v___x_3984_: usize = 0;
    v___x_3982_ = 5usize;
    v___x_3983_ = 1usize;
    v___x_3984_ = lean_usize_shift_left(v___x_3983_, v___x_3982_);
    return v___x_3984_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: usize = 0;
    v___x_3985_ = 1usize;
    v___x_3986_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_3987_ = lean_usize_sub(v___x_3986_, v___x_3985_);
    return v___x_3987_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3988_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_3989_: *mut LeanObject,
    mut v_x_3990_: usize,
    mut v_x_3991_: usize,
    mut v_x_3992_: *mut LeanObject,
    mut v_x_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: usize = 0;
    let mut v___x_3997_: usize = 0;
    let mut v___x_3998_: usize = 0;
    let mut v_j_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_v_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v_node_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4029_: u8 = 0;
    let mut v___x_4030_: usize = 0;
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4049_: u8 = 0;
    let mut v_ks_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: usize = 0;
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: u8 = 0;
    let mut v_reuseFailAlloc_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3989_) == 0 {
                    v_es_3994_ = lean_ctor_get(v_x_3989_, 0);
                    v___x_3995_ = 5usize;
                    v___x_3996_ = 1usize;
                    v___x_3997_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3998_ = lean_usize_land(v_x_3990_, v___x_3997_);
                    v_j_3999_ = lean_usize_to_nat(v___x_3998_);
                    v___x_4000_ = lean_array_get_size(v_es_3994_);
                    v___x_4001_ = lean_nat_dec_lt(v_j_3999_, v___x_4000_);
                    if v___x_4001_ == 0 {
                        lean_dec(v_j_3999_);
                        lean_dec(v_x_3993_);
                        lean_dec(v_x_3992_);
                        return v_x_3989_;
                    } else {
                        lean_inc_ref(v_es_3994_);
                        v_isSharedCheck_4038_ = (!lean_is_exclusive(v_x_3989_)) as u8;
                        if v_isSharedCheck_4038_ == 0 {
                            v_unused_4039_ = lean_ctor_get(v_x_3989_, 0);
                            lean_dec(v_unused_4039_);
                            v___x_4003_ = v_x_3989_;
                            v_isShared_4004_ = v_isSharedCheck_4038_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3989_);
                            v___x_4003_ = lean_box(0);
                            v_isShared_4004_ = v_isSharedCheck_4038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4040_ = lean_ctor_get(v_x_3989_, 0);
                    v_vs_4041_ = lean_ctor_get(v_x_3989_, 1);
                    v_isSharedCheck_4061_ = (!lean_is_exclusive(v_x_3989_)) as u8;
                    if v_isSharedCheck_4061_ == 0 {
                        v___x_4043_ = v_x_3989_;
                        v_isShared_4044_ = v_isSharedCheck_4061_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4041_);
                        lean_inc(v_ks_4040_);
                        lean_dec(v_x_3989_);
                        v___x_4043_ = lean_box(0);
                        v_isShared_4044_ = v_isSharedCheck_4061_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4005_ = lean_array_fget(v_es_3994_, v_j_3999_);
                v___x_4006_ = lean_box(0);
                v_xs_x27_4007_ = lean_array_fset(v_es_3994_, v_j_3999_, v___x_4006_);
                match lean_obj_tag(v_v_4005_) {
                    0 => {
                        v_key_4014_ = lean_ctor_get(v_v_4005_, 0);
                        v_val_4015_ = lean_ctor_get(v_v_4005_, 1);
                        v_isSharedCheck_4025_ = (!lean_is_exclusive(v_v_4005_)) as u8;
                        if v_isSharedCheck_4025_ == 0 {
                            v___x_4017_ = v_v_4005_;
                            v_isShared_4018_ = v_isSharedCheck_4025_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4015_);
                            lean_inc(v_key_4014_);
                            lean_dec(v_v_4005_);
                            v___x_4017_ = lean_box(0);
                            v_isShared_4018_ = v_isSharedCheck_4025_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4026_ = lean_ctor_get(v_v_4005_, 0);
                        v_isSharedCheck_4036_ = (!lean_is_exclusive(v_v_4005_)) as u8;
                        if v_isSharedCheck_4036_ == 0 {
                            v___x_4028_ = v_v_4005_;
                            v_isShared_4029_ = v_isSharedCheck_4036_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4026_);
                            lean_dec(v_v_4005_);
                            v___x_4028_ = lean_box(0);
                            v_isShared_4029_ = v_isSharedCheck_4036_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4037_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4037_, 0, v_x_3992_);
                        lean_ctor_set(v___x_4037_, 1, v_x_3993_);
                        v___y_4009_ = v___x_4037_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4010_ = lean_array_fset(v_xs_x27_4007_, v_j_3999_, v___y_4009_);
                lean_dec(v_j_3999_);
                if v_isShared_4004_ == 0 {
                    lean_ctor_set(v___x_4003_, 0, v___x_4010_);
                    v___x_4012_ = v___x_4003_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
                    v___x_4012_ = v_reuseFailAlloc_4013_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4012_;
            }
            4 => {
                v___x_4019_ = lean_name_eq(v_x_3992_, v_key_4014_);
                if v___x_4019_ == 0 {
                    lean_del_object(v___x_4017_);
                    v___x_4020_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4014_,
                        v_val_4015_,
                        v_x_3992_,
                        v_x_3993_,
                    );
                    v___x_4021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4021_, 0, v___x_4020_);
                    v___y_4009_ = v___x_4021_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4015_);
                    lean_dec(v_key_4014_);
                    if v_isShared_4018_ == 0 {
                        lean_ctor_set(v___x_4017_, 1, v_x_3993_);
                        lean_ctor_set(v___x_4017_, 0, v_x_3992_);
                        v___x_4023_ = v___x_4017_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_x_3992_);
                        lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_x_3993_);
                        v___x_4023_ = v_reuseFailAlloc_4024_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4009_ = v___x_4023_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4030_ = lean_usize_shift_right(v_x_3990_, v___x_3995_);
                v___x_4031_ = lean_usize_add(v_x_3991_, v___x_3996_);
                v___x_4032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_node_4026_, v___x_4030_, v___x_4031_, v_x_3992_, v_x_3993_);
                if v_isShared_4029_ == 0 {
                    lean_ctor_set(v___x_4028_, 0, v___x_4032_);
                    v___x_4034_ = v___x_4028_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4009_ = v___x_4034_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4044_ == 0 {
                    v___x_4046_ = v___x_4043_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_ks_4040_);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_vs_4041_);
                    v___x_4046_ = v_reuseFailAlloc_4060_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4047_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_4046_, v_x_3992_, v_x_3993_);
                v___x_4055_ = 7usize;
                v___x_4056_ = lean_usize_dec_le(v___x_4055_, v_x_3991_);
                if v___x_4056_ == 0 {
                    v___x_4057_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4047_);
                    v___x_4058_ = lean_unsigned_to_nat(4);
                    v___x_4059_ = lean_nat_dec_lt(v___x_4057_, v___x_4058_);
                    lean_dec(v___x_4057_);
                    v___y_4049_ = v___x_4059_;
                    state = 10;
                    continue;
                } else {
                    v___y_4049_ = v___x_4056_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4049_ == 0 {
                    v_ks_4050_ = lean_ctor_get(v_newNode_4047_, 0);
                    lean_inc_ref(v_ks_4050_);
                    v_vs_4051_ = lean_ctor_get(v_newNode_4047_, 1);
                    lean_inc_ref(v_vs_4051_);
                    lean_dec_ref(v_newNode_4047_);
                    v___x_4052_ = lean_unsigned_to_nat(0);
                    v___x_4053_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_4054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3991_, v_ks_4050_, v_vs_4051_, v___x_4052_, v___x_4053_);
                    lean_dec_ref(v_vs_4051_);
                    lean_dec_ref(v_ks_4050_);
                    return v___x_4054_;
                } else {
                    return v_newNode_4047_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_4062_: usize,
    mut v_keys_4063_: *mut LeanObject,
    mut v_vals_4064_: *mut LeanObject,
    mut v_i_4065_: *mut LeanObject,
    mut v_entries_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u8 = 0;
    let mut v_k_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: u64 = 0;
    let mut v_h_4073_: usize = 0;
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: usize = 0;
    let mut v___x_4077_: usize = 0;
    let mut v___x_4078_: usize = 0;
    let mut v_h_4079_: usize = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u64 = 0;
    let mut v_hash_4084_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4067_ = lean_array_get_size(v_keys_4063_);
                v___x_4068_ = lean_nat_dec_lt(v_i_4065_, v___x_4067_);
                if v___x_4068_ == 0 {
                    lean_dec(v_i_4065_);
                    return v_entries_4066_;
                } else {
                    v_k_4069_ = lean_array_fget_borrowed(v_keys_4063_, v_i_4065_);
                    v_v_4070_ = lean_array_fget_borrowed(v_vals_4064_, v_i_4065_);
                    if lean_obj_tag(v_k_4069_) == 0 {
                        v___x_4083_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                        v___y_4072_ = v___x_4083_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4084_ = lean_ctor_get_uint64(
                            v_k_4069_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_4072_ = v_hash_4084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4073_ = lean_uint64_to_usize(v___y_4072_);
                v___x_4074_ = 5usize;
                v___x_4075_ = lean_unsigned_to_nat(1);
                v___x_4076_ = 1usize;
                v___x_4077_ = lean_usize_sub(v_depth_4062_, v___x_4076_);
                v___x_4078_ = lean_usize_mul(v___x_4074_, v___x_4077_);
                v_h_4079_ = lean_usize_shift_right(v_h_4073_, v___x_4078_);
                v___x_4080_ = lean_nat_add(v_i_4065_, v___x_4075_);
                lean_dec(v_i_4065_);
                lean_inc(v_v_4070_);
                lean_inc(v_k_4069_);
                v___x_4081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_entries_4066_, v_h_4079_, v_depth_4062_, v_k_4069_, v_v_4070_);
                v_i_4065_ = v___x_4080_;
                v_entries_4066_ = v___x_4081_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_4085_: *mut LeanObject,
    mut v_keys_4086_: *mut LeanObject,
    mut v_vals_4087_: *mut LeanObject,
    mut v_i_4088_: *mut LeanObject,
    mut v_entries_4089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4090_: usize = 0;
    let mut v_res_4091_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4090_ = lean_unbox_usize(v_depth_4085_);
    lean_dec(v_depth_4085_);
    v_res_4091_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_4090_, v_keys_4086_, v_vals_4087_, v_i_4088_, v_entries_4089_);
    lean_dec_ref(v_vals_4087_);
    lean_dec_ref(v_keys_4086_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4092_: *mut LeanObject,
    mut v_x_4093_: *mut LeanObject,
    mut v_x_4094_: *mut LeanObject,
    mut v_x_4095_: *mut LeanObject,
    mut v_x_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1022__boxed_4097_: usize = 0;
    let mut v_x_1023__boxed_4098_: usize = 0;
    let mut v_res_4099_: *mut LeanObject = core::ptr::null_mut();
    v_x_1022__boxed_4097_ = lean_unbox_usize(v_x_4093_);
    lean_dec(v_x_4093_);
    v_x_1023__boxed_4098_ = lean_unbox_usize(v_x_4094_);
    lean_dec(v_x_4094_);
    v_res_4099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_4092_, v_x_1022__boxed_4097_, v_x_1023__boxed_4098_, v_x_4095_, v_x_4096_);
    return v_res_4099_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(
    mut v_x_4100_: *mut LeanObject,
    mut v_x_4101_: *mut LeanObject,
    mut v_x_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4104_: u64 = 0;
    let mut v___x_4105_: usize = 0;
    let mut v___x_4106_: usize = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u64 = 0;
    let mut v_hash_4109_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4101_) == 0 {
                    v___x_4108_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4104_ = v___x_4108_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4109_ = lean_ctor_get_uint64(
                        v_x_4101_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4104_ = v_hash_4109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4105_ = lean_uint64_to_usize(v___y_4104_);
                v___x_4106_ = 1usize;
                v___x_4107_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_4100_, v___x_4105_, v___x_4106_, v_x_4101_, v_x_4102_);
                return v___x_4107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(
    mut v_x_4110_: *mut LeanObject,
    mut v_x_4111_: *mut LeanObject,
    mut v_x_4112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_4113_: u8 = 0;
    let mut v_map_u2081_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_map_u2081_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4113_ = lean_ctor_get_uint8(
                    v_x_4110_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4113_ == 0 {
                    v_map_u2081_4114_ = lean_ctor_get(v_x_4110_, 0);
                    v_map_u2082_4115_ = lean_ctor_get(v_x_4110_, 1);
                    v_isSharedCheck_4123_ = (!lean_is_exclusive(v_x_4110_)) as u8;
                    if v_isSharedCheck_4123_ == 0 {
                        v___x_4117_ = v_x_4110_;
                        v_isShared_4118_ = v_isSharedCheck_4123_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_4115_);
                        lean_inc(v_map_u2081_4114_);
                        lean_dec(v_x_4110_);
                        v___x_4117_ = lean_box(0);
                        v_isShared_4118_ = v_isSharedCheck_4123_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_4124_ = lean_ctor_get(v_x_4110_, 0);
                    v_map_u2082_4125_ = lean_ctor_get(v_x_4110_, 1);
                    v_isSharedCheck_4133_ = (!lean_is_exclusive(v_x_4110_)) as u8;
                    if v_isSharedCheck_4133_ == 0 {
                        v___x_4127_ = v_x_4110_;
                        v_isShared_4128_ = v_isSharedCheck_4133_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_4125_);
                        lean_inc(v_map_u2081_4124_);
                        lean_dec(v_x_4110_);
                        v___x_4127_ = lean_box(0);
                        v_isShared_4128_ = v_isSharedCheck_4133_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4119_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2082_4115_, v_x_4111_, v_x_4112_);
                if v_isShared_4118_ == 0 {
                    lean_ctor_set(v___x_4117_, 1, v___x_4119_);
                    v___x_4121_ = v___x_4117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_map_u2081_4114_);
                    lean_ctor_set(v_reuseFailAlloc_4122_, 1, v___x_4119_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4122_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_4113_,
                    );
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4121_;
            }
            3 => {
                v___x_4129_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_map_u2081_4124_, v_x_4111_, v_x_4112_);
                if v_isShared_4128_ == 0 {
                    lean_ctor_set(v___x_4127_, 0, v___x_4129_);
                    v___x_4131_ = v___x_4127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                    lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_map_u2082_4125_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4132_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_4113_,
                    );
                    v___x_4131_ = v_reuseFailAlloc_4132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Extension_State_addEntry(
    mut v_s_4134_: *mut LeanObject,
    mut v_e_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    v_name_4136_ = lean_ctor_get(v_e_4135_, 0);
    lean_inc(v_name_4136_);
    v_info_4137_ = lean_ctor_get(v_e_4135_, 1);
    lean_inc_ref(v_info_4137_);
    lean_dec_ref(v_e_4135_);
    v___x_4138_ =
        l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(
            v_s_4134_,
            v_name_4136_,
            v_info_4137_,
        );
    return v___x_4138_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(
    mut v_00_u03b2_4139_: *mut LeanObject,
    mut v_x_4140_: *mut LeanObject,
    mut v_x_4141_: *mut LeanObject,
    mut v_x_4142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    v___x_4143_ =
        l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(
            v_x_4140_, v_x_4141_, v_x_4142_,
        );
    return v___x_4143_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(
    mut v_00_u03b2_4144_: *mut LeanObject,
    mut v_x_4145_: *mut LeanObject,
    mut v_x_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    v___x_4148_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_x_4145_, v_x_4146_, v_x_4147_);
    return v___x_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(
    mut v_00_u03b2_4149_: *mut LeanObject,
    mut v_m_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_b_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_m_4150_, v_a_4151_, v_b_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4154_: *mut LeanObject,
    mut v_x_4155_: *mut LeanObject,
    mut v_x_4156_: usize,
    mut v_x_4157_: usize,
    mut v_x_4158_: *mut LeanObject,
    mut v_x_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_4155_, v_x_4156_, v_x_4157_, v_x_4158_, v_x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4161_: *mut LeanObject,
    mut v_x_4162_: *mut LeanObject,
    mut v_x_4163_: *mut LeanObject,
    mut v_x_4164_: *mut LeanObject,
    mut v_x_4165_: *mut LeanObject,
    mut v_x_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1275__boxed_4167_: usize = 0;
    let mut v_x_1276__boxed_4168_: usize = 0;
    let mut v_res_4169_: *mut LeanObject = core::ptr::null_mut();
    v_x_1275__boxed_4167_ = lean_unbox_usize(v_x_4163_);
    lean_dec(v_x_4163_);
    v_x_1276__boxed_4168_ = lean_unbox_usize(v_x_4164_);
    lean_dec(v_x_4164_);
    v_res_4169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_4161_, v_x_4162_, v_x_1275__boxed_4167_, v_x_1276__boxed_4168_, v_x_4165_, v_x_4166_);
    return v_res_4169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4170_: *mut LeanObject,
    mut v_a_4171_: *mut LeanObject,
    mut v_x_4172_: *mut LeanObject,
) -> u8 {
    let mut v___x_4173_: u8 = 0;
    v___x_4173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_4171_, v_x_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4174_: *mut LeanObject,
    mut v_a_4175_: *mut LeanObject,
    mut v_x_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4177_: u8 = 0;
    let mut v_r_4178_: *mut LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_4174_, v_a_4175_, v_x_4176_);
    lean_dec(v_x_4176_);
    lean_dec(v_a_4175_);
    v_r_4178_ = lean_box((v_res_4177_) as usize);
    return v_r_4178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4179_: *mut LeanObject,
    mut v_data_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_data_4180_);
    return v___x_4181_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
    mut v_b_4184_: *mut LeanObject,
    mut v_x_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_4183_, v_b_4184_, v_x_4185_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4187_: *mut LeanObject,
    mut v_n_4188_: *mut LeanObject,
    mut v_k_4189_: *mut LeanObject,
    mut v_v_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    v___x_4191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4188_, v_k_4189_, v_v_4190_);
    return v___x_4191_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4192_: *mut LeanObject,
    mut v_depth_4193_: usize,
    mut v_keys_4194_: *mut LeanObject,
    mut v_vals_4195_: *mut LeanObject,
    mut v_heq_4196_: *mut LeanObject,
    mut v_i_4197_: *mut LeanObject,
    mut v_entries_4198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    v___x_4199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_4193_, v_keys_4194_, v_vals_4195_, v_i_4197_, v_entries_4198_);
    return v___x_4199_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4200_: *mut LeanObject,
    mut v_depth_4201_: *mut LeanObject,
    mut v_keys_4202_: *mut LeanObject,
    mut v_vals_4203_: *mut LeanObject,
    mut v_heq_4204_: *mut LeanObject,
    mut v_i_4205_: *mut LeanObject,
    mut v_entries_4206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4207_: usize = 0;
    let mut v_res_4208_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4207_ = lean_unbox_usize(v_depth_4201_);
    lean_dec(v_depth_4201_);
    v_res_4208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4200_, v_depth_boxed_4207_, v_keys_4202_, v_vals_4203_, v_heq_4204_, v_i_4205_, v_entries_4206_);
    lean_dec_ref(v_vals_4203_);
    lean_dec_ref(v_keys_4202_);
    return v_res_4208_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_4209_: *mut LeanObject,
    mut v_i_4210_: *mut LeanObject,
    mut v_source_4211_: *mut LeanObject,
    mut v_target_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    v___x_4213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_4210_, v_source_4211_, v_target_4212_);
    return v___x_4213_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4214_: *mut LeanObject,
    mut v_x_4215_: *mut LeanObject,
    mut v_x_4216_: *mut LeanObject,
    mut v_x_4217_: *mut LeanObject,
    mut v_x_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    v___x_4219_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4215_, v_x_4216_, v_x_4217_, v_x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_4220_: *mut LeanObject,
    mut v_x_4221_: *mut LeanObject,
    mut v_x_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    v___x_4223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_4221_, v_x_4222_);
    return v___x_4223_;
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
    mut v_m_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_4225_: u8 = 0;
    let mut v_map_u2081_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4225_ = lean_ctor_get_uint8(
                    v_m_4224_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4225_ == 0 {
                    return v_m_4224_;
                } else {
                    v_map_u2081_4226_ = lean_ctor_get(v_m_4224_, 0);
                    v_map_u2082_4227_ = lean_ctor_get(v_m_4224_, 1);
                    v_isSharedCheck_4235_ = (!lean_is_exclusive(v_m_4224_)) as u8;
                    if v_isSharedCheck_4235_ == 0 {
                        v___x_4229_ = v_m_4224_;
                        v_isShared_4230_ = v_isSharedCheck_4235_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_4227_);
                        lean_inc(v_map_u2081_4226_);
                        lean_dec(v_m_4224_);
                        v___x_4229_ = lean_box(0);
                        v_isShared_4230_ = v_isSharedCheck_4235_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4231_ = 0;
                if v_isShared_4230_ == 0 {
                    v___x_4233_ = v___x_4229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_map_u2081_4226_);
                    lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_map_u2082_4227_);
                    v___x_4233_ = v_reuseFailAlloc_4234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_4233_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_4231_,
                );
                return v___x_4233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(
    mut v_00_u03b2_4236_: *mut LeanObject,
    mut v_m_4237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___x_4238_ =
        l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
            v_m_4237_,
        );
    return v___x_4238_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_State_switch(
    mut v_s_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_4240_ =
        l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
            v_s_4239_,
        );
    return v___x_4240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(
    mut v_env_4241_: *mut LeanObject,
    mut v_as_4242_: *mut LeanObject,
    mut v_i_4243_: usize,
    mut v_stop_4244_: usize,
    mut v_b_4245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4251_ = lean_usize_dec_eq(v_i_4243_, v_stop_4244_);
                if v___x_4251_ == 0 {
                    v___x_4252_ = lean_array_uget_borrowed(v_as_4242_, v_i_4243_);
                    v_name_4253_ = lean_ctor_get(v___x_4252_, 0);
                    v___x_4254_ = 1;
                    lean_inc_ref(v_env_4241_);
                    v___x_4255_ = l_Lean_Environment_setExporting(v_env_4241_, v___x_4254_);
                    lean_inc(v_name_4253_);
                    v___x_4256_ =
                        l_Lean_Environment_contains(v___x_4255_, v_name_4253_, v___x_4251_);
                    if v___x_4256_ == 0 {
                        v___y_4247_ = v_b_4245_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_4252_);
                        v___x_4257_ = lean_array_push(v_b_4245_, v___x_4252_);
                        v___y_4247_ = v___x_4257_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_4241_);
                    return v_b_4245_;
                }
            }
            1 => {
                v___x_4248_ = 1usize;
                v___x_4249_ = lean_usize_add(v_i_4243_, v___x_4248_);
                v_i_4243_ = v___x_4249_;
                v_b_4245_ = v___y_4247_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(
    mut v_env_4258_: *mut LeanObject,
    mut v_as_4259_: *mut LeanObject,
    mut v_i_4260_: *mut LeanObject,
    mut v_stop_4261_: *mut LeanObject,
    mut v_b_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4263_: usize = 0;
    let mut v_stop_boxed_4264_: usize = 0;
    let mut v_res_4265_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4263_ = lean_unbox_usize(v_i_4260_);
    lean_dec(v_i_4260_);
    v_stop_boxed_4264_ = lean_unbox_usize(v_stop_4261_);
    lean_dec(v_stop_4261_);
    v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4258_, v_as_4259_, v_i_boxed_4263_, v_stop_boxed_4264_, v_b_4262_);
    lean_dec_ref(v_as_4259_);
    return v_res_4265_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_env_4268_: *mut LeanObject,
    mut v_x_4269_: *mut LeanObject,
    mut v_entries_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_all_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    v_all_4271_ = lean_array_mk(v_entries_4270_);
    v___x_4272_ = lean_unsigned_to_nat(0);
    v___x_4273_ = lean_array_get_size(v_all_4271_);
    v___x_4274_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_;
    v___x_4275_ = lean_nat_dec_lt(v___x_4272_, v___x_4273_);
    if v___x_4275_ == 0 {
        let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_4268_);
        v___x_4276_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_4276_, 0, v___x_4274_);
        lean_ctor_set(v___x_4276_, 1, v___x_4274_);
        lean_ctor_set(v___x_4276_, 2, v_all_4271_);
        return v___x_4276_;
    } else {
        let mut v___x_4277_: u8 = 0;
        v___x_4277_ = lean_nat_dec_le(v___x_4273_, v___x_4273_);
        if v___x_4277_ == 0 {
            if v___x_4275_ == 0 {
                let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_env_4268_);
                v___x_4278_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4278_, 0, v___x_4274_);
                lean_ctor_set(v___x_4278_, 1, v___x_4274_);
                lean_ctor_set(v___x_4278_, 2, v_all_4271_);
                return v___x_4278_;
            } else {
                let mut v___x_4279_: usize = 0;
                let mut v___x_4280_: usize = 0;
                let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
                v___x_4279_ = 0usize;
                v___x_4280_ = lean_usize_of_nat(v___x_4273_);
                v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4268_, v_all_4271_, v___x_4279_, v___x_4280_, v___x_4274_);
                lean_inc_ref(v___x_4281_);
                v___x_4282_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4282_, 0, v___x_4281_);
                lean_ctor_set(v___x_4282_, 1, v___x_4281_);
                lean_ctor_set(v___x_4282_, 2, v_all_4271_);
                return v___x_4282_;
            }
        } else {
            let mut v___x_4283_: usize = 0;
            let mut v___x_4284_: usize = 0;
            let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
            v___x_4283_ = 0usize;
            v___x_4284_ = lean_usize_of_nat(v___x_4273_);
            v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4268_, v_all_4271_, v___x_4283_, v___x_4284_, v___x_4274_);
            lean_inc_ref(v___x_4285_);
            v___x_4286_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4286_, 0, v___x_4285_);
            lean_ctor_set(v___x_4286_, 1, v___x_4285_);
            lean_ctor_set(v___x_4286_, 2, v_all_4271_);
            return v___x_4286_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(
    mut v_env_4287_: *mut LeanObject,
    mut v_x_4288_: *mut LeanObject,
    mut v_entries_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4290_: *mut LeanObject = core::ptr::null_mut();
    v_res_4290_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_env_4287_, v_x_4288_, v_entries_4289_);
    lean_dec_ref(v_x_4288_);
    return v_res_4290_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_es_4291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    v___x_4292_ = lean_array_mk(v_es_4291_);
    return v___x_4292_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(
    mut v_as_4293_: *mut LeanObject,
    mut v_i_4294_: usize,
    mut v_stop_4295_: usize,
    mut v_b_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4297_: u8 = 0;
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: usize = 0;
    let mut v___x_4301_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4297_ = lean_usize_dec_eq(v_i_4294_, v_stop_4295_);
                if v___x_4297_ == 0 {
                    v___x_4298_ = lean_array_uget_borrowed(v_as_4293_, v_i_4294_);
                    lean_inc(v___x_4298_);
                    v___x_4299_ =
                        l_Lean_Meta_Match_Extension_State_addEntry(v_b_4296_, v___x_4298_);
                    v___x_4300_ = 1usize;
                    v___x_4301_ = lean_usize_add(v_i_4294_, v___x_4300_);
                    v_i_4294_ = v___x_4301_;
                    v_b_4296_ = v___x_4299_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4296_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_as_4303_: *mut LeanObject,
    mut v_i_4304_: *mut LeanObject,
    mut v_stop_4305_: *mut LeanObject,
    mut v_b_4306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4307_: usize = 0;
    let mut v_stop_boxed_4308_: usize = 0;
    let mut v_res_4309_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4307_ = lean_unbox_usize(v_i_4304_);
    lean_dec(v_i_4304_);
    v_stop_boxed_4308_ = lean_unbox_usize(v_stop_4305_);
    lean_dec(v_stop_4305_);
    v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v_as_4303_, v_i_boxed_4307_, v_stop_boxed_4308_, v_b_4306_);
    lean_dec_ref(v_as_4303_);
    return v_res_4309_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(
    mut v_as_4310_: *mut LeanObject,
    mut v_i_4311_: usize,
    mut v_stop_4312_: usize,
    mut v_b_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: usize = 0;
    let mut v___x_4317_: usize = 0;
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: usize = 0;
    let mut v___x_4326_: usize = 0;
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: usize = 0;
    let mut v___x_4329_: usize = 0;
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4319_ = lean_usize_dec_eq(v_i_4311_, v_stop_4312_);
                if v___x_4319_ == 0 {
                    v___x_4320_ = lean_array_uget_borrowed(v_as_4310_, v_i_4311_);
                    v___x_4321_ = lean_unsigned_to_nat(0);
                    v___x_4322_ = lean_array_get_size(v___x_4320_);
                    v___x_4323_ = lean_nat_dec_lt(v___x_4321_, v___x_4322_);
                    if v___x_4323_ == 0 {
                        v___y_4315_ = v_b_4313_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4324_ = lean_nat_dec_le(v___x_4322_, v___x_4322_);
                        if v___x_4324_ == 0 {
                            if v___x_4323_ == 0 {
                                v___y_4315_ = v_b_4313_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4325_ = 0usize;
                                v___x_4326_ = lean_usize_of_nat(v___x_4322_);
                                v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_4320_, v___x_4325_, v___x_4326_, v_b_4313_);
                                v___y_4315_ = v___x_4327_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4328_ = 0usize;
                            v___x_4329_ = lean_usize_of_nat(v___x_4322_);
                            v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_4320_, v___x_4328_, v___x_4329_, v_b_4313_);
                            v___y_4315_ = v___x_4330_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_4313_;
                }
            }
            1 => {
                v___x_4316_ = 1usize;
                v___x_4317_ = lean_usize_add(v_i_4311_, v___x_4316_);
                v_i_4311_ = v___x_4317_;
                v_b_4313_ = v___y_4315_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_as_4331_: *mut LeanObject,
    mut v_i_4332_: *mut LeanObject,
    mut v_stop_4333_: *mut LeanObject,
    mut v_b_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4335_: usize = 0;
    let mut v_stop_boxed_4336_: usize = 0;
    let mut v_res_4337_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4335_ = lean_unbox_usize(v_i_4332_);
    lean_dec(v_i_4332_);
    v_stop_boxed_4336_ = lean_unbox_usize(v_stop_4333_);
    lean_dec(v_stop_4333_);
    v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4331_, v_i_boxed_4335_, v_stop_boxed_4336_, v_b_4334_);
    lean_dec_ref(v_as_4331_);
    return v_res_4337_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(
    mut v_initState_4338_: *mut LeanObject,
    mut v_as_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    v___x_4340_ = lean_unsigned_to_nat(0);
    v___x_4341_ = lean_array_get_size(v_as_4339_);
    v___x_4342_ = lean_nat_dec_lt(v___x_4340_, v___x_4341_);
    if v___x_4342_ == 0 {
        return v_initState_4338_;
    } else {
        let mut v___x_4343_: u8 = 0;
        v___x_4343_ = lean_nat_dec_le(v___x_4341_, v___x_4341_);
        if v___x_4343_ == 0 {
            if v___x_4342_ == 0 {
                return v_initState_4338_;
            } else {
                let mut v___x_4344_: usize = 0;
                let mut v___x_4345_: usize = 0;
                let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
                v___x_4344_ = 0usize;
                v___x_4345_ = lean_usize_of_nat(v___x_4341_);
                v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4339_, v___x_4344_, v___x_4345_, v_initState_4338_);
                return v___x_4346_;
            }
        } else {
            let mut v___x_4347_: usize = 0;
            let mut v___x_4348_: usize = 0;
            let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
            v___x_4347_ = 0usize;
            v___x_4348_ = lean_usize_of_nat(v___x_4341_);
            v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4339_, v___x_4347_, v___x_4348_, v_initState_4338_);
            return v___x_4349_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(
    mut v_initState_4350_: *mut LeanObject,
    mut v_as_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4352_: *mut LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v_initState_4350_, v_as_4351_);
    lean_dec_ref(v_as_4351_);
    return v_res_4352_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_es_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    v___x_4354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4,
    );
    v___x_4355_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v___x_4354_, v_es_4353_);
    v___x_4356_ =
        l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
            v___x_4355_,
        );
    return v___x_4356_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(
    mut v_es_4357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4358_: *mut LeanObject = core::ptr::null_mut();
    v_res_4358_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_es_4357_);
    lean_dec_ref(v_es_4357_);
    return v_res_4358_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    v___x_4387_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_;
    v___x_4388_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(
    mut v_a_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4390_: *mut LeanObject = core::ptr::null_mut();
    v_res_4390_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
    return v_res_4390_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_addMatcherInfo(
    mut v_env_4391_: *mut LeanObject,
    mut v_matcherName_4392_: *mut LeanObject,
    mut v_info_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    v___x_4394_ = l_Lean_Meta_Match_Extension_extension;
    v_toEnvExtension_4395_ = lean_ctor_get(v___x_4394_, 0);
    v_asyncMode_4396_ = lean_ctor_get(v_toEnvExtension_4395_, 2);
    lean_inc(v_matcherName_4392_);
    v___x_4397_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4397_, 0, v_matcherName_4392_);
    lean_ctor_set(v___x_4397_, 1, v_info_4393_);
    v___x_4398_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_4394_,
        v_env_4391_,
        v___x_4397_,
        v_asyncMode_4396_,
        v_matcherName_4392_,
    );
    return v___x_4398_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_4399_: *mut LeanObject,
    mut v_vals_4400_: *mut LeanObject,
    mut v_i_4401_: *mut LeanObject,
    mut v_k_4402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4403_ = lean_array_get_size(v_keys_4399_);
                v___x_4404_ = lean_nat_dec_lt(v_i_4401_, v___x_4403_);
                if v___x_4404_ == 0 {
                    lean_dec(v_i_4401_);
                    v___x_4405_ = lean_box(0);
                    return v___x_4405_;
                } else {
                    v_k_x27_4406_ = lean_array_fget_borrowed(v_keys_4399_, v_i_4401_);
                    v___x_4407_ = lean_name_eq(v_k_4402_, v_k_x27_4406_);
                    if v___x_4407_ == 0 {
                        v___x_4408_ = lean_unsigned_to_nat(1);
                        v___x_4409_ = lean_nat_add(v_i_4401_, v___x_4408_);
                        lean_dec(v_i_4401_);
                        v_i_4401_ = v___x_4409_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4411_ = lean_array_fget_borrowed(v_vals_4400_, v_i_4401_);
                        lean_dec(v_i_4401_);
                        lean_inc(v___x_4411_);
                        v___x_4412_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4412_, 0, v___x_4411_);
                        return v___x_4412_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_4413_: *mut LeanObject,
    mut v_vals_4414_: *mut LeanObject,
    mut v_i_4415_: *mut LeanObject,
    mut v_k_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4417_: *mut LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4413_, v_vals_4414_, v_i_4415_, v_k_4416_);
    lean_dec(v_k_4416_);
    lean_dec_ref(v_vals_4414_);
    lean_dec_ref(v_keys_4413_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_4418_: *mut LeanObject,
    mut v_x_4419_: usize,
    mut v_x_4420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: usize = 0;
    let mut v___x_4424_: usize = 0;
    let mut v___x_4425_: usize = 0;
    let mut v_j_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: usize = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4418_) == 0 {
                    v_es_4421_ = lean_ctor_get(v_x_4418_, 0);
                    v___x_4422_ = lean_box(2);
                    v___x_4423_ = 5usize;
                    v___x_4424_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4425_ = lean_usize_land(v_x_4419_, v___x_4424_);
                    v_j_4426_ = lean_usize_to_nat(v___x_4425_);
                    v___x_4427_ = lean_array_get_borrowed(v___x_4422_, v_es_4421_, v_j_4426_);
                    lean_dec(v_j_4426_);
                    match lean_obj_tag(v___x_4427_) {
                        0 => {
                            v_key_4428_ = lean_ctor_get(v___x_4427_, 0);
                            v_val_4429_ = lean_ctor_get(v___x_4427_, 1);
                            v___x_4430_ = lean_name_eq(v_x_4420_, v_key_4428_);
                            if v___x_4430_ == 0 {
                                v___x_4431_ = lean_box(0);
                                return v___x_4431_;
                            } else {
                                lean_inc(v_val_4429_);
                                v___x_4432_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4432_, 0, v_val_4429_);
                                return v___x_4432_;
                            }
                        }
                        1 => {
                            v_node_4433_ = lean_ctor_get(v___x_4427_, 0);
                            v___x_4434_ = lean_usize_shift_right(v_x_4419_, v___x_4423_);
                            v_x_4418_ = v_node_4433_;
                            v_x_4419_ = v___x_4434_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4436_ = lean_box(0);
                            return v___x_4436_;
                        }
                    }
                } else {
                    v_ks_4437_ = lean_ctor_get(v_x_4418_, 0);
                    v_vs_4438_ = lean_ctor_get(v_x_4418_, 1);
                    v___x_4439_ = lean_unsigned_to_nat(0);
                    v___x_4440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4437_, v_vs_4438_, v___x_4439_, v_x_4420_);
                    return v___x_4440_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4441_: *mut LeanObject,
    mut v_x_4442_: *mut LeanObject,
    mut v_x_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_573__boxed_4444_: usize = 0;
    let mut v_res_4445_: *mut LeanObject = core::ptr::null_mut();
    v_x_573__boxed_4444_ = lean_unbox_usize(v_x_4442_);
    lean_dec(v_x_4442_);
    v_res_4445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_4441_, v_x_573__boxed_4444_, v_x_4443_);
    lean_dec(v_x_4443_);
    lean_dec_ref(v_x_4441_);
    return v_res_4445_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(
    mut v_x_4446_: *mut LeanObject,
    mut v_x_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4449_: u64 = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u64 = 0;
    let mut v_hash_4453_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4447_) == 0 {
                    v___x_4452_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4449_ = v___x_4452_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4453_ = lean_ctor_get_uint64(
                        v_x_4447_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4449_ = v_hash_4453_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4450_ = lean_uint64_to_usize(v___y_4449_);
                v___x_4451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_4446_, v___x_4450_, v_x_4447_);
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4454_: *mut LeanObject,
    mut v_x_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4456_: *mut LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_4454_, v_x_4455_);
    lean_dec(v_x_4455_);
    lean_dec_ref(v_x_4454_);
    return v_res_4456_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(
    mut v_a_4457_: *mut LeanObject,
    mut v_x_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4458_) == 0 {
                    v___x_4459_ = lean_box(0);
                    return v___x_4459_;
                } else {
                    v_key_4460_ = lean_ctor_get(v_x_4458_, 0);
                    v_value_4461_ = lean_ctor_get(v_x_4458_, 1);
                    v_tail_4462_ = lean_ctor_get(v_x_4458_, 2);
                    v___x_4463_ = lean_name_eq(v_key_4460_, v_a_4457_);
                    if v___x_4463_ == 0 {
                        v_x_4458_ = v_tail_4462_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4461_);
                        v___x_4465_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4465_, 0, v_value_4461_);
                        return v___x_4465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_4466_: *mut LeanObject,
    mut v_x_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_4466_, v_x_4467_);
    lean_dec(v_x_4467_);
    lean_dec(v_a_4466_);
    return v_res_4468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(
    mut v_m_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4474_: u64 = 0;
    let mut v___x_4475_: u64 = 0;
    let mut v___x_4476_: u64 = 0;
    let mut v_fold_4477_: u64 = 0;
    let mut v___x_4478_: u64 = 0;
    let mut v___x_4479_: u64 = 0;
    let mut v___x_4480_: u64 = 0;
    let mut v___x_4481_: usize = 0;
    let mut v___x_4482_: usize = 0;
    let mut v___x_4483_: usize = 0;
    let mut v___x_4484_: usize = 0;
    let mut v___x_4485_: usize = 0;
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: u64 = 0;
    let mut v_hash_4489_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4471_ = lean_ctor_get(v_m_4469_, 1);
                v___x_4472_ = lean_array_get_size(v_buckets_4471_);
                if lean_obj_tag(v_a_4470_) == 0 {
                    v___x_4488_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4474_ = v___x_4488_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4489_ = lean_ctor_get_uint64(
                        v_a_4470_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4474_ = v_hash_4489_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4475_ = 32u64;
                v___x_4476_ = lean_uint64_shift_right(v___y_4474_, v___x_4475_);
                v_fold_4477_ = lean_uint64_xor(v___y_4474_, v___x_4476_);
                v___x_4478_ = 16u64;
                v___x_4479_ = lean_uint64_shift_right(v_fold_4477_, v___x_4478_);
                v___x_4480_ = lean_uint64_xor(v_fold_4477_, v___x_4479_);
                v___x_4481_ = lean_uint64_to_usize(v___x_4480_);
                v___x_4482_ = lean_usize_of_nat(v___x_4472_);
                v___x_4483_ = 1usize;
                v___x_4484_ = lean_usize_sub(v___x_4482_, v___x_4483_);
                v___x_4485_ = lean_usize_land(v___x_4481_, v___x_4484_);
                v___x_4486_ = lean_array_uget_borrowed(v_buckets_4471_, v___x_4485_);
                v___x_4487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_4470_, v___x_4486_);
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(
    mut v_m_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4492_: *mut LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_4490_, v_a_4491_);
    lean_dec(v_a_4491_);
    lean_dec_ref(v_m_4490_);
    return v_res_4492_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
    mut v_x_4493_: *mut LeanObject,
    mut v_x_4494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_4495_: u8 = 0;
    v_stage_u2081_4495_ = lean_ctor_get_uint8(
        v_x_4493_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4495_ == 0 {
        let mut v_map_u2081_4496_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_4496_ = lean_ctor_get(v_x_4493_, 0);
        v_map_u2082_4497_ = lean_ctor_get(v_x_4493_, 1);
        v___x_4498_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_4497_, v_x_4494_);
        if lean_obj_tag(v___x_4498_) == 0 {
            let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
            v___x_4499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_4496_, v_x_4494_);
            return v___x_4499_;
        } else {
            return v___x_4498_;
        }
    } else {
        let mut v_map_u2081_4500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_4500_ = lean_ctor_get(v_x_4493_, 0);
        v___x_4501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_4500_, v_x_4494_);
        return v___x_4501_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(
    mut v_x_4502_: *mut LeanObject,
    mut v_x_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4504_: *mut LeanObject = core::ptr::null_mut();
    v_res_4504_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
            v_x_4502_, v_x_4503_,
        );
    lean_dec(v_x_4503_);
    lean_dec_ref(v_x_4502_);
    return v_res_4504_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1() -> *mut LeanObject
{
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4506_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0;
    v___x_4507_ = lean_string_utf8_byte_size(v___x_4506_);
    return v___x_4507_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(
    mut v_env_4508_: *mut LeanObject,
    mut v_declName_4509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_4509_);
    v___x_4510_ = lean_erase_macro_scopes(v_declName_4509_);
    if lean_obj_tag(v___x_4510_) == 1 {
        let mut v_str_4511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4515_: u8 = 0;
        v_str_4511_ = lean_ctor_get(v___x_4510_, 1);
        lean_inc_ref(v_str_4511_);
        lean_dec_ref_known(v___x_4510_, 2);
        v___x_4512_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0;
        v___x_4513_ = lean_string_utf8_byte_size(v_str_4511_);
        v___x_4514_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once
            ),
            _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1,
        );
        v___x_4515_ = lean_nat_dec_le(v___x_4514_, v___x_4513_);
        if v___x_4515_ == 0 {
            let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_str_4511_);
            lean_dec(v_declName_4509_);
            lean_dec_ref(v_env_4508_);
            v___x_4516_ = lean_box(0);
            return v___x_4516_;
        } else {
            let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4518_: u8 = 0;
            v___x_4517_ = lean_unsigned_to_nat(0);
            v___x_4518_ = lean_string_memcmp(
                v_str_4511_,
                v___x_4512_,
                v___x_4517_,
                v___x_4517_,
                v___x_4514_,
            );
            lean_dec_ref(v_str_4511_);
            if v___x_4518_ == 0 {
                let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_declName_4509_);
                lean_dec_ref(v_env_4508_);
                v___x_4519_ = lean_box(0);
                return v___x_4519_;
            } else {
                let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toEnvExtension_4521_: *mut LeanObject = core::ptr::null_mut();
                let mut v_asyncMode_4522_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
                v___x_4520_ = l_Lean_Meta_Match_Extension_extension;
                v_toEnvExtension_4521_ = lean_ctor_get(v___x_4520_, 0);
                v_asyncMode_4522_ = lean_ctor_get(v_toEnvExtension_4521_, 2);
                v___x_4523_ = l_Lean_Meta_Match_Extension_instInhabitedState;
                lean_inc(v_declName_4509_);
                v___x_4524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4523_,
                    v___x_4520_,
                    v_env_4508_,
                    v_asyncMode_4522_,
                    v_declName_4509_,
                );
                v___x_4525_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_4524_, v_declName_4509_);
                lean_dec(v_declName_4509_);
                lean_dec(v___x_4524_);
                return v___x_4525_;
            }
        }
    } else {
        let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_4510_);
        lean_dec(v_declName_4509_);
        lean_dec_ref(v_env_4508_);
        v___x_4526_ = lean_box(0);
        return v___x_4526_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(
    mut v_00_u03b2_4527_: *mut LeanObject,
    mut v_x_4528_: *mut LeanObject,
    mut v_x_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    v___x_4530_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
            v_x_4528_, v_x_4529_,
        );
    return v___x_4530_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(
    mut v_00_u03b2_4531_: *mut LeanObject,
    mut v_x_4532_: *mut LeanObject,
    mut v_x_4533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4534_: *mut LeanObject = core::ptr::null_mut();
    v_res_4534_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(
            v_00_u03b2_4531_,
            v_x_4532_,
            v_x_4533_,
        );
    lean_dec(v_x_4533_);
    lean_dec_ref(v_x_4532_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(
    mut v_00_u03b2_4535_: *mut LeanObject,
    mut v_x_4536_: *mut LeanObject,
    mut v_x_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    v___x_4538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_4536_, v_x_4537_);
    return v___x_4538_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4539_: *mut LeanObject,
    mut v_x_4540_: *mut LeanObject,
    mut v_x_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4542_: *mut LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_4539_, v_x_4540_, v_x_4541_);
    lean_dec(v_x_4541_);
    lean_dec_ref(v_x_4540_);
    return v_res_4542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(
    mut v_00_u03b2_4543_: *mut LeanObject,
    mut v_m_4544_: *mut LeanObject,
    mut v_a_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_4544_, v_a_4545_);
    return v___x_4546_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(
    mut v_00_u03b2_4547_: *mut LeanObject,
    mut v_m_4548_: *mut LeanObject,
    mut v_a_4549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4550_: *mut LeanObject = core::ptr::null_mut();
    v_res_4550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_4547_, v_m_4548_, v_a_4549_);
    lean_dec(v_a_4549_);
    lean_dec_ref(v_m_4548_);
    return v_res_4550_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4551_: *mut LeanObject,
    mut v_x_4552_: *mut LeanObject,
    mut v_x_4553_: usize,
    mut v_x_4554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_4552_, v_x_4553_, v_x_4554_);
    return v___x_4555_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4556_: *mut LeanObject,
    mut v_x_4557_: *mut LeanObject,
    mut v_x_4558_: *mut LeanObject,
    mut v_x_4559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_775__boxed_4560_: usize = 0;
    let mut v_res_4561_: *mut LeanObject = core::ptr::null_mut();
    v_x_775__boxed_4560_ = lean_unbox_usize(v_x_4558_);
    lean_dec(v_x_4558_);
    v_res_4561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4556_, v_x_4557_, v_x_775__boxed_4560_, v_x_4559_);
    lean_dec(v_x_4559_);
    lean_dec_ref(v_x_4557_);
    return v_res_4561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4562_: *mut LeanObject,
    mut v_a_4563_: *mut LeanObject,
    mut v_x_4564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    v___x_4565_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_4563_, v_x_4564_);
    return v___x_4565_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4566_: *mut LeanObject,
    mut v_a_4567_: *mut LeanObject,
    mut v_x_4568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4569_: *mut LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_4566_, v_a_4567_, v_x_4568_);
    lean_dec(v_x_4568_);
    lean_dec(v_a_4567_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4570_: *mut LeanObject,
    mut v_keys_4571_: *mut LeanObject,
    mut v_vals_4572_: *mut LeanObject,
    mut v_heq_4573_: *mut LeanObject,
    mut v_i_4574_: *mut LeanObject,
    mut v_k_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    v___x_4576_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4571_, v_vals_4572_, v_i_4574_, v_k_4575_);
    return v___x_4576_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4577_: *mut LeanObject,
    mut v_keys_4578_: *mut LeanObject,
    mut v_vals_4579_: *mut LeanObject,
    mut v_heq_4580_: *mut LeanObject,
    mut v_i_4581_: *mut LeanObject,
    mut v_k_4582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4583_: *mut LeanObject = core::ptr::null_mut();
    v_res_4583_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4577_, v_keys_4578_, v_vals_4579_, v_heq_4580_, v_i_4581_, v_k_4582_);
    lean_dec(v_k_4582_);
    lean_dec_ref(v_vals_4579_);
    lean_dec_ref(v_keys_4578_);
    return v_res_4583_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(
    mut v_matcherName_4584_: *mut LeanObject,
    mut v_info_4585_: *mut LeanObject,
    mut v_env_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    v___x_4587_ =
        l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_4586_, v_matcherName_4584_, v_info_4585_);
    return v___x_4587_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___redArg(
    mut v_inst_4588_: *mut LeanObject,
    mut v_matcherName_4589_: *mut LeanObject,
    mut v_info_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_4591_ = lean_ctor_get(v_inst_4588_, 1);
    lean_inc(v_modifyEnv_4591_);
    lean_dec_ref(v_inst_4588_);
    v___f_4592_ = lean_alloc_closure(
        l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4592_, 0, v_matcherName_4589_);
    lean_closure_set(v___f_4592_, 1, v_info_4590_);
    v___x_4593_ = lean_apply_1(v_modifyEnv_4591_, v___f_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo(
    mut v_m_4594_: *mut LeanObject,
    mut v_inst_4595_: *mut LeanObject,
    mut v_inst_4596_: *mut LeanObject,
    mut v_matcherName_4597_: *mut LeanObject,
    mut v_info_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    v___x_4599_ =
        l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_4596_, v_matcherName_4597_, v_info_4598_);
    return v___x_4599_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___boxed(
    mut v_m_4600_: *mut LeanObject,
    mut v_inst_4601_: *mut LeanObject,
    mut v_inst_4602_: *mut LeanObject,
    mut v_matcherName_4603_: *mut LeanObject,
    mut v_info_4604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4605_: *mut LeanObject = core::ptr::null_mut();
    v_res_4605_ = l_Lean_Meta_Match_addMatcherInfo(
        v_m_4600_,
        v_inst_4601_,
        v_inst_4602_,
        v_matcherName_4603_,
        v_info_4604_,
    );
    lean_dec_ref(v_inst_4601_);
    return v_res_4605_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfoCore_x3f(
    mut v_env_4606_: *mut LeanObject,
    mut v_declName_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    v___x_4608_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4606_, v_declName_4607_);
    return v___x_4608_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(
    mut v_declName_4609_: *mut LeanObject,
    mut v_toPure_4610_: *mut LeanObject,
    mut v_____do__lift_4611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    v___x_4612_ =
        l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_4611_, v_declName_4609_);
    v___x_4613_ = lean_apply_2(v_toPure_4610_, lean_box(0), v___x_4612_);
    return v___x_4613_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___redArg(
    mut v_inst_4614_: *mut LeanObject,
    mut v_inst_4615_: *mut LeanObject,
    mut v_declName_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4617_ = lean_ctor_get(v_inst_4614_, 0);
    lean_inc_ref(v_toApplicative_4617_);
    v_toBind_4618_ = lean_ctor_get(v_inst_4614_, 1);
    lean_inc(v_toBind_4618_);
    lean_dec_ref(v_inst_4614_);
    v_getEnv_4619_ = lean_ctor_get(v_inst_4615_, 0);
    lean_inc(v_getEnv_4619_);
    lean_dec_ref(v_inst_4615_);
    v_toPure_4620_ = lean_ctor_get(v_toApplicative_4617_, 1);
    lean_inc(v_toPure_4620_);
    lean_dec_ref(v_toApplicative_4617_);
    v___f_4621_ = lean_alloc_closure(
        l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4621_, 0, v_declName_4616_);
    lean_closure_set(v___f_4621_, 1, v_toPure_4620_);
    v___x_4622_ = lean_apply_4(
        v_toBind_4618_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4619_,
        v___f_4621_,
    );
    return v___x_4622_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f(
    mut v_m_4623_: *mut LeanObject,
    mut v_inst_4624_: *mut LeanObject,
    mut v_inst_4625_: *mut LeanObject,
    mut v_declName_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    v___x_4627_ =
        l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4624_, v_inst_4625_, v_declName_4626_);
    return v___x_4627_;
}
pub unsafe fn lean_is_matcher(
    mut v_env_4628_: *mut LeanObject,
    mut v_declName_4629_: *mut LeanObject,
) -> u8 {
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4628_, v_declName_4629_);
    if lean_obj_tag(v___x_4630_) == 0 {
        let mut v___x_4631_: u8 = 0;
        v___x_4631_ = 0;
        return v___x_4631_;
    } else {
        let mut v___x_4632_: u8 = 0;
        lean_dec_ref_known(v___x_4630_, 1);
        v___x_4632_ = 1;
        return v___x_4632_;
    }
}
pub unsafe fn l_Lean_Meta_isMatcherCore___boxed(
    mut v_env_4633_: *mut LeanObject,
    mut v_declName_4634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4635_: u8 = 0;
    let mut v_r_4636_: *mut LeanObject = core::ptr::null_mut();
    v_res_4635_ = lean_is_matcher(v_env_4633_, v_declName_4634_);
    v_r_4636_ = lean_box((v_res_4635_) as usize);
    return v_r_4636_;
}
pub unsafe fn l_Lean_Meta_isMatcher___redArg___lam__0(
    mut v_declName_4637_: *mut LeanObject,
    mut v_toPure_4638_: *mut LeanObject,
    mut v_____do__lift_4639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    v___x_4640_ = lean_is_matcher(v_____do__lift_4639_, v_declName_4637_);
    v___x_4641_ = lean_box((v___x_4640_) as usize);
    v___x_4642_ = lean_apply_2(v_toPure_4638_, lean_box(0), v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Lean_Meta_isMatcher___redArg(
    mut v_inst_4643_: *mut LeanObject,
    mut v_inst_4644_: *mut LeanObject,
    mut v_declName_4645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4646_ = lean_ctor_get(v_inst_4643_, 0);
    lean_inc_ref(v_toApplicative_4646_);
    v_toBind_4647_ = lean_ctor_get(v_inst_4643_, 1);
    lean_inc(v_toBind_4647_);
    lean_dec_ref(v_inst_4643_);
    v_getEnv_4648_ = lean_ctor_get(v_inst_4644_, 0);
    lean_inc(v_getEnv_4648_);
    lean_dec_ref(v_inst_4644_);
    v_toPure_4649_ = lean_ctor_get(v_toApplicative_4646_, 1);
    lean_inc(v_toPure_4649_);
    lean_dec_ref(v_toApplicative_4646_);
    v___f_4650_ = lean_alloc_closure(
        l_Lean_Meta_isMatcher___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4650_, 0, v_declName_4645_);
    lean_closure_set(v___f_4650_, 1, v_toPure_4649_);
    v___x_4651_ = lean_apply_4(
        v_toBind_4647_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4648_,
        v___f_4650_,
    );
    return v___x_4651_;
}
pub unsafe fn l_Lean_Meta_isMatcher(
    mut v_m_4652_: *mut LeanObject,
    mut v_inst_4653_: *mut LeanObject,
    mut v_inst_4654_: *mut LeanObject,
    mut v_declName_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    v___x_4656_ = l_Lean_Meta_isMatcher___redArg(v_inst_4653_, v_inst_4654_, v_declName_4655_);
    return v___x_4656_;
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore_x3f(
    mut v_env_4657_: *mut LeanObject,
    mut v_e_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    v_fn_4659_ = l_Lean_Expr_getAppFn(v_e_4658_);
    v___x_4660_ = l_Lean_Expr_isConst(v_fn_4659_);
    if v___x_4660_ == 0 {
        let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_fn_4659_);
        lean_dec_ref(v_env_4657_);
        v___x_4661_ = lean_box(0);
        return v___x_4661_;
    } else {
        let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
        v___x_4662_ = l_Lean_Expr_constName_x21(v_fn_4659_);
        lean_dec_ref(v_fn_4659_);
        v___x_4663_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4657_, v___x_4662_);
        if lean_obj_tag(v___x_4663_) == 1 {
            let mut v_val_4664_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4667_: u8 = 0;
            v_val_4664_ = lean_ctor_get(v___x_4663_, 0);
            lean_inc(v_val_4664_);
            v___x_4665_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_4664_);
            lean_dec(v_val_4664_);
            v___x_4666_ = l_Lean_Expr_getAppNumArgs(v_e_4658_);
            v___x_4667_ = lean_nat_dec_le(v___x_4665_, v___x_4666_);
            lean_dec(v___x_4666_);
            lean_dec(v___x_4665_);
            if v___x_4667_ == 0 {
                let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_4663_, 1);
                v___x_4668_ = lean_box(0);
                return v___x_4668_;
            } else {
                return v___x_4663_;
            }
        } else {
            let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4663_);
            v___x_4669_ = lean_box(0);
            return v___x_4669_;
        }
    }
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore_x3f___boxed(
    mut v_env_4670_: *mut LeanObject,
    mut v_e_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4672_: *mut LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_4670_, v_e_4671_);
    lean_dec_ref(v_e_4671_);
    return v_res_4672_;
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore(
    mut v_env_4673_: *mut LeanObject,
    mut v_e_4674_: *mut LeanObject,
) -> u8 {
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    v___x_4675_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_4673_, v_e_4674_);
    if lean_obj_tag(v___x_4675_) == 0 {
        let mut v___x_4676_: u8 = 0;
        v___x_4676_ = 0;
        return v___x_4676_;
    } else {
        let mut v___x_4677_: u8 = 0;
        lean_dec_ref_known(v___x_4675_, 1);
        v___x_4677_ = 1;
        return v___x_4677_;
    }
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore___boxed(
    mut v_env_4678_: *mut LeanObject,
    mut v_e_4679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4680_: u8 = 0;
    let mut v_r_4681_: *mut LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Lean_Meta_isMatcherAppCore(v_env_4678_, v_e_4679_);
    lean_dec_ref(v_e_4679_);
    v_r_4681_ = lean_box((v_res_4680_) as usize);
    return v_r_4681_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg___lam__0(
    mut v_e_4682_: *mut LeanObject,
    mut v_toPure_4683_: *mut LeanObject,
    mut v_____do__lift_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    v___x_4685_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_4684_, v_e_4682_);
    v___x_4686_ = lean_box((v___x_4685_) as usize);
    v___x_4687_ = lean_apply_2(v_toPure_4683_, lean_box(0), v___x_4686_);
    return v___x_4687_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(
    mut v_e_4688_: *mut LeanObject,
    mut v_toPure_4689_: *mut LeanObject,
    mut v_____do__lift_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_4688_, v_toPure_4689_, v_____do__lift_4690_);
    lean_dec_ref(v_e_4688_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg(
    mut v_inst_4692_: *mut LeanObject,
    mut v_inst_4693_: *mut LeanObject,
    mut v_e_4694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4695_ = lean_ctor_get(v_inst_4692_, 0);
    lean_inc_ref(v_toApplicative_4695_);
    v_toBind_4696_ = lean_ctor_get(v_inst_4692_, 1);
    lean_inc(v_toBind_4696_);
    lean_dec_ref(v_inst_4692_);
    v_getEnv_4697_ = lean_ctor_get(v_inst_4693_, 0);
    lean_inc(v_getEnv_4697_);
    lean_dec_ref(v_inst_4693_);
    v_toPure_4698_ = lean_ctor_get(v_toApplicative_4695_, 1);
    lean_inc(v_toPure_4698_);
    lean_dec_ref(v_toApplicative_4695_);
    v___f_4699_ = lean_alloc_closure(
        l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4699_, 0, v_e_4694_);
    lean_closure_set(v___f_4699_, 1, v_toPure_4698_);
    v___x_4700_ = lean_apply_4(
        v_toBind_4696_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4697_,
        v___f_4699_,
    );
    return v___x_4700_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp(
    mut v_m_4701_: *mut LeanObject,
    mut v_inst_4702_: *mut LeanObject,
    mut v_inst_4703_: *mut LeanObject,
    mut v_e_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4705_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_4702_, v_inst_4703_, v_e_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    v___x_4712_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_;
    v___x_4713_ = lean_box(0);
    v___x_4714_ = l_Lean_mkTagDeclarationExtension(v___x_4712_, v___x_4713_);
    return v___x_4714_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(
    mut v_a_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4716_: *mut LeanObject = core::ptr::null_mut();
    v_res_4716_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
    return v_res_4716_;
}
pub unsafe fn l_Lean_Meta_markMatcherLike(
    mut v_env_4717_: *mut LeanObject,
    mut v_declName_4718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Lean_Meta_matcherLikeExt;
    v___x_4720_ = l_Lean_TagDeclarationExtension_tag(v___x_4719_, v_env_4717_, v_declName_4718_);
    return v___x_4720_;
}
pub unsafe fn l_Lean_Meta_isMatcherLikeCore(
    mut v_env_4721_: *mut LeanObject,
    mut v_declName_4722_: *mut LeanObject,
) -> u8 {
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: u8 = 0;
    v___x_4723_ = l_Lean_Meta_matcherLikeExt;
    v_toEnvExtension_4724_ = lean_ctor_get(v___x_4723_, 0);
    v_asyncMode_4725_ = lean_ctor_get(v_toEnvExtension_4724_, 2);
    v___x_4726_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_4723_,
        v_env_4721_,
        v_declName_4722_,
        v_asyncMode_4725_,
    );
    return v___x_4726_;
}
pub unsafe fn l_Lean_Meta_isMatcherLikeCore___boxed(
    mut v_env_4727_: *mut LeanObject,
    mut v_declName_4728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4729_: u8 = 0;
    let mut v_r_4730_: *mut LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Lean_Meta_isMatcherLikeCore(v_env_4727_, v_declName_4728_);
    v_r_4730_ = lean_box((v_res_4729_) as usize);
    return v_r_4730_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___redArg___lam__0(
    mut v_declName_4731_: *mut LeanObject,
    mut v_toPure_4732_: *mut LeanObject,
    mut v_____do__lift_4733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    v___x_4734_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_4733_, v_declName_4731_);
    v___x_4735_ = lean_box((v___x_4734_) as usize);
    v___x_4736_ = lean_apply_2(v_toPure_4732_, lean_box(0), v___x_4735_);
    return v___x_4736_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___redArg(
    mut v_inst_4737_: *mut LeanObject,
    mut v_inst_4738_: *mut LeanObject,
    mut v_declName_4739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4740_ = lean_ctor_get(v_inst_4737_, 0);
    lean_inc_ref(v_toApplicative_4740_);
    v_toBind_4741_ = lean_ctor_get(v_inst_4737_, 1);
    lean_inc(v_toBind_4741_);
    lean_dec_ref(v_inst_4737_);
    v_getEnv_4742_ = lean_ctor_get(v_inst_4738_, 0);
    lean_inc(v_getEnv_4742_);
    lean_dec_ref(v_inst_4738_);
    v_toPure_4743_ = lean_ctor_get(v_toApplicative_4740_, 1);
    lean_inc(v_toPure_4743_);
    lean_dec_ref(v_toApplicative_4740_);
    v___f_4744_ = lean_alloc_closure(
        l_Lean_Meta_isMatcherLike___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4744_, 0, v_declName_4739_);
    lean_closure_set(v___f_4744_, 1, v_toPure_4743_);
    v___x_4745_ = lean_apply_4(
        v_toBind_4741_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4742_,
        v___f_4744_,
    );
    return v___x_4745_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike(
    mut v_m_4746_: *mut LeanObject,
    mut v_inst_4747_: *mut LeanObject,
    mut v_inst_4748_: *mut LeanObject,
    mut v_declName_4749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_4747_, v_inst_4748_, v_declName_4749_);
    return v___x_4750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Match_instInhabitedDiscrInfo_default =
        _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo_default);
    l_Lean_Meta_Match_instInhabitedDiscrInfo = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo);
    l_Lean_Meta_Match_instInhabitedOverlaps_default =
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps_default);
    l_Lean_Meta_Match_instInhabitedOverlaps = _init_l_Lean_Meta_Match_instInhabitedOverlaps();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps);
    l_Lean_Meta_Match_instInhabitedMatcherInfo_default =
        _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo_default);
    l_Lean_Meta_Match_instInhabitedMatcherInfo = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo);
    l_Lean_Meta_Match_Extension_instInhabitedState =
        _init_l_Lean_Meta_Match_Extension_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Match_Extension_instInhabitedState);
    res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Match_Extension_extension = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Match_Extension_extension);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_matcherLikeExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_matcherLikeExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatcherInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_MatcherInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatcherInfo(builtin);
}
