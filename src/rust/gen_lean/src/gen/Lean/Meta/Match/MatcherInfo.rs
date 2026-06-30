// Lean compiler output
// Module: Lean.Meta.Match.MatcherInfo
// Imports: Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_nat_to_int, lean_string_length, lean_string_memcmp,
    lean_string_utf8_byte_size, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::lean_erase_macro_scopes;
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
pub static mut l_Lean_Meta_Match_instInhabitedDiscrInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedDiscrInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value:
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
    m_data: [104, 78, 97, 109, 101, 63, 0],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instReprDiscrInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instReprDiscrInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedOverlaps_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedOverlaps: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 111, 102, 76, 105, 115, 116, 32, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprOverlaps___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Match_instReprOverlaps_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instReprOverlaps___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instReprOverlaps: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprOverlaps___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Meta_Match_Overlaps_overlapping___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltParamInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value:
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
    m_data: [104, 97, 115, 85, 110, 105, 116, 84, 104, 117, 110, 107, 0],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value:
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
    m_fun: l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instReprAltParamInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instReprAltParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value:
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
    m_fun: l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instBEqAltParamInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instBEqAltParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value:
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
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatcherInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatcherInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value:
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
    m_data: [97, 108, 116, 73, 110, 102, 111, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value:
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
    m_data: [100, 105, 115, 99, 114, 73, 110, 102, 111, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value:
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
    m_data: [111, 118, 101, 114, 108, 97, 112, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value:
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
    m_fun: l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instReprMatcherInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instReprMatcherInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_instInhabitedState___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_Extension_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5431323822491600447 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3008809457587767149 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18229679040985057098 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Match_Extension_State_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_Extension_extension: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value:
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
    m_data: [109, 97, 116, 99, 104, 95, 0],
};
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 97, 116, 99, 104, 101, 114, 76, 105, 107, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1902021009172655898 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_matcherLikeExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = leanh::lean_box(0);
    return v___x_2376_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedDiscrInfo() -> *mut leanh::LeanObject {
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = leanh::lean_box(0);
    return v___x_2377_;
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(
    mut v_x_2384_: *mut leanh::LeanObject,
    mut v_x_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2384_) == 0 {
        let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2386_ =
            l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1;
        return v___x_2386_;
    } else {
        let mut v_val_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2387_ = leanh::lean_ctor_get(v_x_2384_, 0);
        leanh::lean_inc(v_val_2387_);
        leanh::lean_dec_ref_known(v_x_2384_, 1);
        v___x_2388_ =
            l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3;
        v___x_2389_ = leanh::lean_unsigned_to_nat(1024);
        v___x_2390_ = l_Lean_Name_reprPrec(v_val_2387_, v___x_2389_);
        v___x_2391_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2391_, 0, v___x_2388_);
        leanh::lean_ctor_set(v___x_2391_, 1, v___x_2390_);
        v___x_2392_ = l_Repr_addAppParen(v___x_2391_, v_x_2385_);
        return v___x_2392_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(
    mut v_x_2393_: *mut leanh::LeanObject,
    mut v_x_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ =
        l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_2393_, v_x_2394_);
    leanh::lean_dec(v_x_2394_);
    return v_res_2395_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(
    mut v_a_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = lean_nat_to_int(v_a_2396_);
    return v___x_2397_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = leanh::lean_unsigned_to_nat(10);
    v___x_2412_ = lean_nat_to_int(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0;
    v___x_2415_ = lean_string_length(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9,
    );
    v___x_2417_ = lean_nat_to_int(v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(
    mut v_x_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6;
    v___x_2424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7,
    );
    v___x_2425_ = leanh::lean_unsigned_to_nat(0);
    v___x_2426_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(
        v_x_2422_,
        v___x_2425_,
    );
    v___x_2427_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2427_, 0, v___x_2424_);
    leanh::lean_ctor_set(v___x_2427_, 1, v___x_2426_);
    v___x_2428_ = 0;
    v___x_2429_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2429_, 0, v___x_2427_);
    leanh::lean_ctor_set_uint8(
        v___x_2429_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2428_,
    );
    v___x_2430_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2430_, 0, v___x_2423_);
    leanh::lean_ctor_set(v___x_2430_, 1, v___x_2429_);
    v___x_2431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_2432_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_2433_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2433_, 0, v___x_2432_);
    leanh::lean_ctor_set(v___x_2433_, 1, v___x_2430_);
    v___x_2434_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_2435_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2435_, 0, v___x_2433_);
    leanh::lean_ctor_set(v___x_2435_, 1, v___x_2434_);
    v___x_2436_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2436_, 0, v___x_2431_);
    leanh::lean_ctor_set(v___x_2436_, 1, v___x_2435_);
    v___x_2437_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2437_, 0, v___x_2436_);
    leanh::lean_ctor_set_uint8(
        v___x_2437_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2428_,
    );
    return v___x_2437_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr(
    mut v_x_2438_: *mut leanh::LeanObject,
    mut v_prec_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_x_2438_);
    return v___x_2440_;
}
pub unsafe fn l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(
    mut v_x_2441_: *mut leanh::LeanObject,
    mut v_prec_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Meta_Match_instReprDiscrInfo_repr(v_x_2441_, v_prec_2442_);
    leanh::lean_dec(v_prec_2442_);
    return v_res_2443_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = leanh::lean_box(0);
    v___x_2447_ = leanh::lean_unsigned_to_nat(16);
    v___x_2448_ = lean_mk_array(v___x_2447_, v___x_2446_);
    return v___x_2448_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once),
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0,
    );
    v___x_2450_ = leanh::lean_unsigned_to_nat(0);
    v___x_2451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
    leanh::lean_ctor_set(v___x_2451_, 1, v___x_2449_);
    return v___x_2451_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps_default()
-> *mut leanh::LeanObject {
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once),
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1,
    );
    return v___x_2452_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedOverlaps() -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
    return v___x_2453_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(
    mut v_x_2454_: *mut leanh::LeanObject,
    mut v_x_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2455_) == 0 {
        leanh::lean_inc(v_x_2454_);
        return v_x_2454_;
    } else {
        let mut v_key_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_2456_ = leanh::lean_ctor_get(v_x_2455_, 0);
        v_value_2457_ = leanh::lean_ctor_get(v_x_2455_, 1);
        v_tail_2458_ = leanh::lean_ctor_get(v_x_2455_, 2);
        v___x_2459_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_2454_, v_tail_2458_);
        leanh::lean_inc(v_value_2457_);
        leanh::lean_inc(v_key_2456_);
        v___x_2460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2460_, 0, v_key_2456_);
        leanh::lean_ctor_set(v___x_2460_, 1, v_value_2457_);
        v___x_2461_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2461_, 0, v___x_2460_);
        leanh::lean_ctor_set(v___x_2461_, 1, v___x_2459_);
        return v___x_2461_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(
    mut v_x_2462_: *mut leanh::LeanObject,
    mut v_x_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_2462_, v_x_2463_);
    leanh::lean_dec(v_x_2463_);
    leanh::lean_dec(v_x_2462_);
    return v_res_2464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(
    mut v_as_2465_: *mut leanh::LeanObject,
    mut v_i_2466_: usize,
    mut v_stop_2467_: usize,
    mut v_b_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec(v_b_2468_);
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
    mut v_as_2475_: *mut leanh::LeanObject,
    mut v_i_2476_: *mut leanh::LeanObject,
    mut v_stop_2477_: *mut leanh::LeanObject,
    mut v_b_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2479_: usize = 0;
    let mut v_stop_boxed_2480_: usize = 0;
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2479_ = leanh::lean_unbox_usize(v_i_2476_);
    leanh::lean_dec(v_i_2476_);
    v_stop_boxed_2480_ = leanh::lean_unbox_usize(v_stop_2477_);
    leanh::lean_dec(v_stop_2477_);
    v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_2475_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2478_);
    leanh::lean_dec_ref(v_as_2475_);
    return v_res_2481_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(
    mut v_x_2482_: *mut leanh::LeanObject,
    mut v_x_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2484_) == 0 {
                    leanh::lean_dec(v_x_2482_);
                    return v_x_2483_;
                } else {
                    v_head_2485_ = leanh::lean_ctor_get(v_x_2484_, 0);
                    v_tail_2486_ = leanh::lean_ctor_get(v_x_2484_, 1);
                    v_isSharedCheck_2497_ = (!leanh::lean_is_exclusive(v_x_2484_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v___x_2488_ = v_x_2484_;
                        v_isShared_2489_ = v_isSharedCheck_2497_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2486_);
                        leanh::lean_inc(v_head_2485_);
                        leanh::lean_dec(v_x_2484_);
                        v___x_2488_ = leanh::lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2497_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2482_);
                if v_isShared_2489_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2488_, 5);
                    leanh::lean_ctor_set(v___x_2488_, 1, v_x_2482_);
                    leanh::lean_ctor_set(v___x_2488_, 0, v_x_2483_);
                    v___x_2491_ = v___x_2488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_x_2483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_x_2482_);
                    v___x_2491_ = v_reuseFailAlloc_2496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2492_ = l_Nat_reprFast(v_head_2485_);
                v___x_2493_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
                v___x_2494_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2494_, 0, v___x_2491_);
                leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
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
    mut v_x_2498_: *mut leanh::LeanObject,
    mut v_x_2499_: *mut leanh::LeanObject,
    mut v_x_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2500_) == 0 {
                    leanh::lean_dec(v_x_2498_);
                    return v_x_2499_;
                } else {
                    v_head_2501_ = leanh::lean_ctor_get(v_x_2500_, 0);
                    v_tail_2502_ = leanh::lean_ctor_get(v_x_2500_, 1);
                    v_isSharedCheck_2513_ = (!leanh::lean_is_exclusive(v_x_2500_)) as u8;
                    if v_isSharedCheck_2513_ == 0 {
                        v___x_2504_ = v_x_2500_;
                        v_isShared_2505_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2502_);
                        leanh::lean_inc(v_head_2501_);
                        leanh::lean_dec(v_x_2500_);
                        v___x_2504_ = leanh::lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2498_);
                if v_isShared_2505_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2504_, 5);
                    leanh::lean_ctor_set(v___x_2504_, 1, v_x_2498_);
                    leanh::lean_ctor_set(v___x_2504_, 0, v_x_2499_);
                    v___x_2507_ = v___x_2504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_x_2499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_x_2498_);
                    v___x_2507_ = v_reuseFailAlloc_2512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2508_ = l_Nat_reprFast(v_head_2501_);
                v___x_2509_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2509_, 0, v___x_2508_);
                v___x_2510_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2510_, 0, v___x_2507_);
                leanh::lean_ctor_set(v___x_2510_, 1, v___x_2509_);
                v___x_2511_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(v_x_2498_, v___x_2510_, v_tail_2502_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(
    mut v___y_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Nat_reprFast(v___y_2514_);
    v___x_2516_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(
    mut v_x_2517_: *mut leanh::LeanObject,
    mut v_x_2518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2517_) == 0 {
        let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2518_);
        v___x_2519_ = leanh::lean_box(0);
        return v___x_2519_;
    } else {
        let mut v_tail_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2520_ = leanh::lean_ctor_get(v_x_2517_, 1);
        if leanh::lean_obj_tag(v_tail_2520_) == 0 {
            let mut v_head_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2518_);
            v_head_2521_ = leanh::lean_ctor_get(v_x_2517_, 0);
            leanh::lean_inc(v_head_2521_);
            leanh::lean_dec_ref_known(v_x_2517_, 2);
            v___x_2522_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2521_);
            return v___x_2522_;
        } else {
            let mut v_head_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2520_);
            v_head_2523_ = leanh::lean_ctor_get(v_x_2517_, 0);
            leanh::lean_inc(v_head_2523_);
            leanh::lean_dec_ref_known(v_x_2517_, 2);
            v___x_2524_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2523_);
            v___x_2525_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(v_x_2518_, v___x_2524_, v_tail_2520_);
            return v___x_2525_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_2538_ = lean_string_length(v___x_2537_);
    return v___x_2538_;
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7);
    v___x_2540_ = lean_nat_to_int(v___x_2539_);
    return v___x_2540_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(
    mut v_a_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2545_) == 0 {
        let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2546_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1;
        return v___x_2546_;
    } else {
        let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2555_: u8 = 0;
        let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2547_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_2548_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(v_a_2545_, v___x_2547_);
        v___x_2549_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
        v___x_2550_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9;
        v___x_2551_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
        leanh::lean_ctor_set(v___x_2551_, 1, v___x_2548_);
        v___x_2552_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_2553_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2553_, 0, v___x_2551_);
        leanh::lean_ctor_set(v___x_2553_, 1, v___x_2552_);
        v___x_2554_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2554_, 0, v___x_2549_);
        leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
        v___x_2555_ = 0;
        v___x_2556_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2556_, 0, v___x_2554_);
        leanh::lean_ctor_set_uint8(
            v___x_2556_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2555_,
        );
        return v___x_2556_;
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(
    mut v_x_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2559_) == 0 {
                    leanh::lean_dec(v_x_2557_);
                    return v_x_2558_;
                } else {
                    v_head_2560_ = leanh::lean_ctor_get(v_x_2559_, 0);
                    v_tail_2561_ = leanh::lean_ctor_get(v_x_2559_, 1);
                    v_isSharedCheck_2570_ = (!leanh::lean_is_exclusive(v_x_2559_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2563_ = v_x_2559_;
                        v_isShared_2564_ = v_isSharedCheck_2570_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2561_);
                        leanh::lean_inc(v_head_2560_);
                        leanh::lean_dec(v_x_2559_);
                        v___x_2563_ = leanh::lean_box(0);
                        v_isShared_2564_ = v_isSharedCheck_2570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2557_);
                if v_isShared_2564_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2563_, 5);
                    leanh::lean_ctor_set(v___x_2563_, 1, v_x_2557_);
                    leanh::lean_ctor_set(v___x_2563_, 0, v_x_2558_);
                    v___x_2566_ = v___x_2563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_x_2558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_x_2557_);
                    v___x_2566_ = v_reuseFailAlloc_2569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2567_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                leanh::lean_ctor_set(v___x_2567_, 1, v_head_2560_);
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
    mut v_x_2571_: *mut leanh::LeanObject,
    mut v_x_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2571_) == 0 {
        let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2572_);
        v___x_2573_ = leanh::lean_box(0);
        return v___x_2573_;
    } else {
        let mut v_tail_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2574_ = leanh::lean_ctor_get(v_x_2571_, 1);
        if leanh::lean_obj_tag(v_tail_2574_) == 0 {
            let mut v_head_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2572_);
            v_head_2575_ = leanh::lean_ctor_get(v_x_2571_, 0);
            leanh::lean_inc(v_head_2575_);
            leanh::lean_dec_ref_known(v_x_2571_, 2);
            return v_head_2575_;
        } else {
            let mut v_head_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2574_);
            v_head_2576_ = leanh::lean_ctor_get(v_x_2571_, 0);
            leanh::lean_inc(v_head_2576_);
            leanh::lean_dec_ref_known(v_x_2571_, 2);
            v___x_2577_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(v_x_2572_, v_head_2576_, v_tail_2574_);
            return v___x_2577_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(
    mut v_init_2578_: *mut leanh::LeanObject,
    mut v_x_2579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2579_) == 0 {
                    v_k_2580_ = leanh::lean_ctor_get(v_x_2579_, 1);
                    v_l_2581_ = leanh::lean_ctor_get(v_x_2579_, 3);
                    v_r_2582_ = leanh::lean_ctor_get(v_x_2579_, 4);
                    v___x_2583_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_2578_, v_r_2582_);
                    leanh::lean_inc(v_k_2580_);
                    v___x_2584_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2584_, 0, v_k_2580_);
                    leanh::lean_ctor_set(v___x_2584_, 1, v___x_2583_);
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
    mut v_init_2586_: *mut leanh::LeanObject,
    mut v_x_2587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2588_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_2586_, v_x_2587_);
    leanh::lean_dec(v_x_2587_);
    return v_res_2588_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2595_ = lean_string_length(v___x_2594_);
    return v___x_2595_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4);
    v___x_2597_ = lean_nat_to_int(v___x_2596_);
    return v___x_2597_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(
    mut v_x_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2603_ = leanh::lean_ctor_get(v_x_2602_, 0);
                v_snd_2604_ = leanh::lean_ctor_get(v_x_2602_, 1);
                v_isSharedCheck_2632_ = (!leanh::lean_is_exclusive(v_x_2602_)) as u8;
                if v_isSharedCheck_2632_ == 0 {
                    v___x_2606_ = v_x_2602_;
                    v_isShared_2607_ = v_isSharedCheck_2632_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2604_);
                    leanh::lean_inc(v_fst_2603_);
                    leanh::lean_dec(v_x_2602_);
                    v___x_2606_ = leanh::lean_box(0);
                    v_isShared_2607_ = v_isSharedCheck_2632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2608_ = l_Nat_reprFast(v_fst_2603_);
                v___x_2609_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2609_, 0, v___x_2608_);
                v___x_2610_ = leanh::lean_box(0);
                if v_isShared_2607_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2606_, 1);
                    leanh::lean_ctor_set(v___x_2606_, 1, v___x_2610_);
                    leanh::lean_ctor_set(v___x_2606_, 0, v___x_2609_);
                    v___x_2612_ = v___x_2606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2610_);
                    v___x_2612_ = v_reuseFailAlloc_2631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2613_ = leanh::lean_unsigned_to_nat(0);
                v___x_2614_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2;
                v___x_2615_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v___x_2610_, v_snd_2604_);
                leanh::lean_dec(v_snd_2604_);
                v___x_2616_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v___x_2615_);
                v___x_2617_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2617_, 0, v___x_2614_);
                leanh::lean_ctor_set(v___x_2617_, 1, v___x_2616_);
                v___x_2618_ = l_Repr_addAppParen(v___x_2617_, v___x_2613_);
                v___x_2619_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2619_, 0, v___x_2618_);
                leanh::lean_ctor_set(v___x_2619_, 1, v___x_2612_);
                v___x_2620_ = l_List_reverse___redArg(v___x_2619_);
                v___x_2621_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
                v___x_2622_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(v___x_2620_, v___x_2621_);
                v___x_2623_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5);
                v___x_2624_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6;
                v___x_2625_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2625_, 0, v___x_2624_);
                leanh::lean_ctor_set(v___x_2625_, 1, v___x_2622_);
                v___x_2626_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7;
                v___x_2627_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2628_, 0, v___x_2623_);
                leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = 0;
                v___x_2630_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2630_, 0, v___x_2628_);
                leanh::lean_ctor_set_uint8(
                    v___x_2630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2629_,
                );
                return v___x_2630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(
    mut v_x_2633_: *mut leanh::LeanObject,
    mut v_x_2634_: *mut leanh::LeanObject,
    mut v_x_2635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2635_) == 0 {
                    leanh::lean_dec(v_x_2633_);
                    return v_x_2634_;
                } else {
                    v_head_2636_ = leanh::lean_ctor_get(v_x_2635_, 0);
                    v_tail_2637_ = leanh::lean_ctor_get(v_x_2635_, 1);
                    v_isSharedCheck_2647_ = (!leanh::lean_is_exclusive(v_x_2635_)) as u8;
                    if v_isSharedCheck_2647_ == 0 {
                        v___x_2639_ = v_x_2635_;
                        v_isShared_2640_ = v_isSharedCheck_2647_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2637_);
                        leanh::lean_inc(v_head_2636_);
                        leanh::lean_dec(v_x_2635_);
                        v___x_2639_ = leanh::lean_box(0);
                        v_isShared_2640_ = v_isSharedCheck_2647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2633_);
                if v_isShared_2640_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2639_, 5);
                    leanh::lean_ctor_set(v___x_2639_, 1, v_x_2633_);
                    leanh::lean_ctor_set(v___x_2639_, 0, v_x_2634_);
                    v___x_2642_ = v___x_2639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_x_2634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_x_2633_);
                    v___x_2642_ = v_reuseFailAlloc_2646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2643_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2636_);
                v___x_2644_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2644_, 0, v___x_2642_);
                leanh::lean_ctor_set(v___x_2644_, 1, v___x_2643_);
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
    mut v_x_2648_: *mut leanh::LeanObject,
    mut v_x_2649_: *mut leanh::LeanObject,
    mut v_x_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2650_) == 0 {
                    leanh::lean_dec(v_x_2648_);
                    return v_x_2649_;
                } else {
                    v_head_2651_ = leanh::lean_ctor_get(v_x_2650_, 0);
                    v_tail_2652_ = leanh::lean_ctor_get(v_x_2650_, 1);
                    v_isSharedCheck_2662_ = (!leanh::lean_is_exclusive(v_x_2650_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2654_ = v_x_2650_;
                        v_isShared_2655_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2652_);
                        leanh::lean_inc(v_head_2651_);
                        leanh::lean_dec(v_x_2650_);
                        v___x_2654_ = leanh::lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2648_);
                if v_isShared_2655_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2654_, 5);
                    leanh::lean_ctor_set(v___x_2654_, 1, v_x_2648_);
                    leanh::lean_ctor_set(v___x_2654_, 0, v_x_2649_);
                    v___x_2657_ = v___x_2654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_x_2649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_x_2648_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2658_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2651_);
                v___x_2659_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2659_, 0, v___x_2657_);
                leanh::lean_ctor_set(v___x_2659_, 1, v___x_2658_);
                v___x_2660_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(v_x_2648_, v___x_2659_, v_tail_2652_);
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(
    mut v_x_2663_: *mut leanh::LeanObject,
    mut v_x_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2663_) == 0 {
        let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2664_);
        v___x_2665_ = leanh::lean_box(0);
        return v___x_2665_;
    } else {
        let mut v_tail_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2666_ = leanh::lean_ctor_get(v_x_2663_, 1);
        if leanh::lean_obj_tag(v_tail_2666_) == 0 {
            let mut v_head_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2664_);
            v_head_2667_ = leanh::lean_ctor_get(v_x_2663_, 0);
            leanh::lean_inc(v_head_2667_);
            leanh::lean_dec_ref_known(v_x_2663_, 2);
            v___x_2668_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2667_);
            return v___x_2668_;
        } else {
            let mut v_head_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2666_);
            v_head_2669_ = leanh::lean_ctor_get(v_x_2663_, 0);
            leanh::lean_inc(v_head_2669_);
            leanh::lean_dec_ref_known(v_x_2663_, 2);
            v___x_2670_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_2669_);
            v___x_2671_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(v_x_2664_, v___x_2670_, v_tail_2666_);
            return v___x_2671_;
        }
    }
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(
    mut v_a_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2672_) == 0 {
        let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2673_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1;
        return v___x_2673_;
    } else {
        let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2674_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_2675_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(v_a_2672_, v___x_2674_);
        v___x_2676_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
        v___x_2677_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9;
        v___x_2678_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2678_, 0, v___x_2677_);
        leanh::lean_ctor_set(v___x_2678_, 1, v___x_2675_);
        v___x_2679_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_2680_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2680_, 0, v___x_2678_);
        leanh::lean_ctor_set(v___x_2680_, 1, v___x_2679_);
        v___x_2681_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2681_, 0, v___x_2676_);
        leanh::lean_ctor_set(v___x_2681_, 1, v___x_2680_);
        v___x_2682_ = 0;
        v___x_2683_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2683_, 0, v___x_2681_);
        leanh::lean_ctor_set_uint8(
            v___x_2683_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2682_,
        );
        return v___x_2683_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = leanh::lean_unsigned_to_nat(7);
    v___x_2694_ = lean_nat_to_int(v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr___redArg(
    mut v_x_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    let mut v___x_2728_: usize = 0;
    let mut v___x_2729_: usize = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_unused_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2699_ = leanh::lean_ctor_get(v_x_2698_, 1);
                v_isSharedCheck_2731_ = (!leanh::lean_is_exclusive(v_x_2698_)) as u8;
                if v_isSharedCheck_2731_ == 0 {
                    v_unused_2732_ = leanh::lean_ctor_get(v_x_2698_, 0);
                    leanh::lean_dec(v_unused_2732_);
                    v___x_2701_ = v_x_2698_;
                    v_isShared_2702_ = v_isSharedCheck_2731_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2699_);
                    leanh::lean_dec(v_x_2698_);
                    v___x_2701_ = leanh::lean_box(0);
                    v_isShared_2702_ = v_isSharedCheck_2731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2703_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3;
                v___x_2704_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4,
                );
                v___x_2705_ = leanh::lean_unsigned_to_nat(0);
                v___x_2706_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6;
                v___x_2725_ = leanh::lean_box(0);
                v___x_2726_ = lean_array_get_size(v_buckets_2699_);
                v___x_2727_ = lean_nat_dec_lt(v___x_2705_, v___x_2726_);
                if v___x_2727_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2699_);
                    v___y_2708_ = v___x_2725_;
                    state = 2;
                    continue;
                } else {
                    v___x_2728_ = lean_usize_of_nat(v___x_2726_);
                    v___x_2729_ = 0usize;
                    v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_buckets_2699_, v___x_2728_, v___x_2729_, v___x_2725_);
                    leanh::lean_dec_ref(v_buckets_2699_);
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
                    leanh::lean_ctor_set_tag(v___x_2701_, 5);
                    leanh::lean_ctor_set(v___x_2701_, 1, v___x_2709_);
                    leanh::lean_ctor_set(v___x_2701_, 0, v___x_2706_);
                    v___x_2711_ = v___x_2701_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2709_);
                    v___x_2711_ = v_reuseFailAlloc_2724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2712_ = l_Repr_addAppParen(v___x_2711_, v___x_2705_);
                v___x_2713_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2713_, 0, v___x_2704_);
                leanh::lean_ctor_set(v___x_2713_, 1, v___x_2712_);
                v___x_2714_ = 0;
                v___x_2715_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2715_, 0, v___x_2713_);
                leanh::lean_ctor_set_uint8(
                    v___x_2715_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2714_,
                );
                v___x_2716_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2716_, 0, v___x_2703_);
                leanh::lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                v___x_2717_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
                );
                v___x_2718_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
                v___x_2719_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2719_, 0, v___x_2718_);
                leanh::lean_ctor_set(v___x_2719_, 1, v___x_2716_);
                v___x_2720_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
                v___x_2721_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2721_, 0, v___x_2719_);
                leanh::lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                v___x_2722_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2722_, 0, v___x_2717_);
                leanh::lean_ctor_set(v___x_2722_, 1, v___x_2721_);
                v___x_2723_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2723_, 0, v___x_2722_);
                leanh::lean_ctor_set_uint8(
                    v___x_2723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2714_,
                );
                return v___x_2723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr(
    mut v_x_2733_: *mut leanh::LeanObject,
    mut v_prec_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2735_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_2733_);
    return v___x_2735_;
}
pub unsafe fn l_Lean_Meta_Match_instReprOverlaps_repr___boxed(
    mut v_x_2736_: *mut leanh::LeanObject,
    mut v_prec_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_2736_, v_prec_2737_);
    leanh::lean_dec(v_prec_2737_);
    return v_res_2738_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(
    mut v_a_2739_: *mut leanh::LeanObject,
    mut v_n_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ =
        l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v_a_2739_);
    return v___x_2741_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_n_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2744_ =
        l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_a_2742_, v_n_2743_);
    leanh::lean_dec(v_n_2743_);
    return v_res_2744_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(
    mut v_x_2745_: *mut leanh::LeanObject,
    mut v_x_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_x_2745_);
    return v___x_2747_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(
    mut v_x_2748_: *mut leanh::LeanObject,
    mut v_x_2749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2750_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(v_x_2748_, v_x_2749_);
    leanh::lean_dec(v_x_2749_);
    return v_res_2750_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(
    mut v_a_2751_: *mut leanh::LeanObject,
    mut v_n_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v_a_2751_);
    return v___x_2753_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(
    mut v_a_2754_: *mut leanh::LeanObject,
    mut v_n_2755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(v_a_2754_, v_n_2755_);
    leanh::lean_dec(v_n_2755_);
    return v_res_2756_;
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_isEmpty(
    mut v_o_2759_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    v_size_2760_ = leanh::lean_ctor_get(v_o_2759_, 0);
    v___x_2761_ = leanh::lean_unsigned_to_nat(0);
    v___x_2762_ = lean_nat_dec_eq(v_size_2760_, v___x_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_isEmpty___boxed(
    mut v_o_2763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2764_: u8 = 0;
    let mut v_r_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2764_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_2763_);
    leanh::lean_dec_ref(v_o_2763_);
    v_r_2765_ = leanh::lean_box((v_res_2764_) as usize);
    return v_r_2765_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(
    mut v_k_2766_: *mut leanh::LeanObject,
    mut v_t_2767_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2767_) == 0 {
                    v_k_2768_ = leanh::lean_ctor_get(v_t_2767_, 1);
                    v_l_2769_ = leanh::lean_ctor_get(v_t_2767_, 3);
                    v_r_2770_ = leanh::lean_ctor_get(v_t_2767_, 4);
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
    mut v_k_2776_: *mut leanh::LeanObject,
    mut v_t_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2778_: u8 = 0;
    let mut v_r_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_2776_, v_t_2777_);
    leanh::lean_dec(v_t_2777_);
    leanh::lean_dec(v_k_2776_);
    v_r_2779_ = leanh::lean_box((v_res_2778_) as usize);
    return v_r_2779_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(
    mut v_k_2780_: *mut leanh::LeanObject,
    mut v_v_2781_: *mut leanh::LeanObject,
    mut v_t_2782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: u8 = 0;
    let mut v_impl_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v_size_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2823_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v_unused_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v_unused_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v_k_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_unused_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_unused_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_unused_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v_size_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_unused_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_unused_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_unused_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3040_: u8 = 0;
    let mut v_k_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v_unused_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_unused_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2782_) == 0 {
                    v_size_2783_ = leanh::lean_ctor_get(v_t_2782_, 0);
                    v_k_2784_ = leanh::lean_ctor_get(v_t_2782_, 1);
                    v_v_2785_ = leanh::lean_ctor_get(v_t_2782_, 2);
                    v_l_2786_ = leanh::lean_ctor_get(v_t_2782_, 3);
                    v_r_2787_ = leanh::lean_ctor_get(v_t_2782_, 4);
                    v_isSharedCheck_3068_ = (!leanh::lean_is_exclusive(v_t_2782_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_2789_ = v_t_2782_;
                        v_isShared_2790_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2787_);
                        leanh::lean_inc(v_l_2786_);
                        leanh::lean_inc(v_v_2785_);
                        leanh::lean_inc(v_k_2784_);
                        leanh::lean_inc(v_size_2783_);
                        leanh::lean_dec(v_t_2782_);
                        v___x_2789_ = leanh::lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3069_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3070_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3070_, 0, v___x_3069_);
                    leanh::lean_ctor_set(v___x_3070_, 1, v_k_2780_);
                    leanh::lean_ctor_set(v___x_3070_, 2, v_v_2781_);
                    leanh::lean_ctor_set(v___x_3070_, 3, v_t_2782_);
                    leanh::lean_ctor_set(v___x_3070_, 4, v_t_2782_);
                    return v___x_3070_;
                }
            }
            1 => {
                v___x_2791_ = lean_nat_dec_lt(v_k_2780_, v_k_2784_);
                if v___x_2791_ == 0 {
                    v___x_2792_ = lean_nat_dec_eq(v_k_2780_, v_k_2784_);
                    if v___x_2792_ == 0 {
                        leanh::lean_dec(v_size_2783_);
                        v_impl_2793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_2780_, v_v_2781_, v_r_2787_);
                        v___x_2794_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_2786_) == 0 {
                            v_size_2795_ = leanh::lean_ctor_get(v_l_2786_, 0);
                            v_size_2796_ = leanh::lean_ctor_get(v_impl_2793_, 0);
                            leanh::lean_inc(v_size_2796_);
                            v_k_2797_ = leanh::lean_ctor_get(v_impl_2793_, 1);
                            leanh::lean_inc(v_k_2797_);
                            v_v_2798_ = leanh::lean_ctor_get(v_impl_2793_, 2);
                            leanh::lean_inc(v_v_2798_);
                            v_l_2799_ = leanh::lean_ctor_get(v_impl_2793_, 3);
                            leanh::lean_inc(v_l_2799_);
                            v_r_2800_ = leanh::lean_ctor_get(v_impl_2793_, 4);
                            leanh::lean_inc(v_r_2800_);
                            v___x_2801_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2802_ = lean_nat_mul(v___x_2801_, v_size_2795_);
                            v___x_2803_ = lean_nat_dec_lt(v___x_2802_, v_size_2796_);
                            leanh::lean_dec(v___x_2802_);
                            if v___x_2803_ == 0 {
                                leanh::lean_dec(v_r_2800_);
                                leanh::lean_dec(v_l_2799_);
                                leanh::lean_dec(v_v_2798_);
                                leanh::lean_dec(v_k_2797_);
                                v___x_2804_ = lean_nat_add(v___x_2794_, v_size_2795_);
                                v___x_2805_ = lean_nat_add(v___x_2804_, v_size_2796_);
                                leanh::lean_dec(v_size_2796_);
                                leanh::lean_dec(v___x_2804_);
                                if v_isShared_2790_ == 0 {
                                    leanh::lean_ctor_set(v___x_2789_, 4, v_impl_2793_);
                                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2805_);
                                    v___x_2807_ = v___x_2789_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2808_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2808_,
                                        0,
                                        v___x_2805_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2808_,
                                        1,
                                        v_k_2784_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2808_,
                                        2,
                                        v_v_2785_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2808_,
                                        3,
                                        v_l_2786_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2808_,
                                        4,
                                        v_impl_2793_,
                                    );
                                    v___x_2807_ = v_reuseFailAlloc_2808_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2872_ =
                                    (!leanh::lean_is_exclusive(v_impl_2793_)) as u8;
                                if v_isSharedCheck_2872_ == 0 {
                                    v_unused_2873_ = leanh::lean_ctor_get(v_impl_2793_, 4);
                                    leanh::lean_dec(v_unused_2873_);
                                    v_unused_2874_ = leanh::lean_ctor_get(v_impl_2793_, 3);
                                    leanh::lean_dec(v_unused_2874_);
                                    v_unused_2875_ = leanh::lean_ctor_get(v_impl_2793_, 2);
                                    leanh::lean_dec(v_unused_2875_);
                                    v_unused_2876_ = leanh::lean_ctor_get(v_impl_2793_, 1);
                                    leanh::lean_dec(v_unused_2876_);
                                    v_unused_2877_ = leanh::lean_ctor_get(v_impl_2793_, 0);
                                    leanh::lean_dec(v_unused_2877_);
                                    v___x_2810_ = v_impl_2793_;
                                    v_isShared_2811_ = v_isSharedCheck_2872_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2793_);
                                    v___x_2810_ = leanh::lean_box(0);
                                    v_isShared_2811_ = v_isSharedCheck_2872_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2878_ = leanh::lean_ctor_get(v_impl_2793_, 3);
                            leanh::lean_inc(v_l_2878_);
                            if leanh::lean_obj_tag(v_l_2878_) == 0 {
                                v_r_2879_ = leanh::lean_ctor_get(v_impl_2793_, 4);
                                v_k_2880_ = leanh::lean_ctor_get(v_impl_2793_, 1);
                                v_v_2881_ = leanh::lean_ctor_get(v_impl_2793_, 2);
                                v_isSharedCheck_2904_ =
                                    (!leanh::lean_is_exclusive(v_impl_2793_)) as u8;
                                if v_isSharedCheck_2904_ == 0 {
                                    v_unused_2905_ = leanh::lean_ctor_get(v_impl_2793_, 3);
                                    leanh::lean_dec(v_unused_2905_);
                                    v_unused_2906_ = leanh::lean_ctor_get(v_impl_2793_, 0);
                                    leanh::lean_dec(v_unused_2906_);
                                    v___x_2883_ = v_impl_2793_;
                                    v_isShared_2884_ = v_isSharedCheck_2904_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2879_);
                                    leanh::lean_inc(v_v_2881_);
                                    leanh::lean_inc(v_k_2880_);
                                    leanh::lean_dec(v_impl_2793_);
                                    v___x_2883_ = leanh::lean_box(0);
                                    v_isShared_2884_ = v_isSharedCheck_2904_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2907_ = leanh::lean_ctor_get(v_impl_2793_, 4);
                                leanh::lean_inc(v_r_2907_);
                                if leanh::lean_obj_tag(v_r_2907_) == 0 {
                                    v_k_2908_ = leanh::lean_ctor_get(v_impl_2793_, 1);
                                    v_v_2909_ = leanh::lean_ctor_get(v_impl_2793_, 2);
                                    v_isSharedCheck_2920_ =
                                        (!leanh::lean_is_exclusive(v_impl_2793_)) as u8;
                                    if v_isSharedCheck_2920_ == 0 {
                                        v_unused_2921_ =
                                            leanh::lean_ctor_get(v_impl_2793_, 4);
                                        leanh::lean_dec(v_unused_2921_);
                                        v_unused_2922_ =
                                            leanh::lean_ctor_get(v_impl_2793_, 3);
                                        leanh::lean_dec(v_unused_2922_);
                                        v_unused_2923_ =
                                            leanh::lean_ctor_get(v_impl_2793_, 0);
                                        leanh::lean_dec(v_unused_2923_);
                                        v___x_2911_ = v_impl_2793_;
                                        v_isShared_2912_ = v_isSharedCheck_2920_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2909_);
                                        leanh::lean_inc(v_k_2908_);
                                        leanh::lean_dec(v_impl_2793_);
                                        v___x_2911_ = leanh::lean_box(0);
                                        v_isShared_2912_ = v_isSharedCheck_2920_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_2924_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2790_ == 0 {
                                        leanh::lean_ctor_set(v___x_2789_, 4, v_impl_2793_);
                                        leanh::lean_ctor_set(v___x_2789_, 3, v_r_2907_);
                                        leanh::lean_ctor_set(v___x_2789_, 0, v___x_2924_);
                                        v___x_2926_ = v___x_2789_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2927_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2927_,
                                            0,
                                            v___x_2924_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2927_,
                                            1,
                                            v_k_2784_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2927_,
                                            2,
                                            v_v_2785_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2927_,
                                            3,
                                            v_r_2907_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2927_,
                                            4,
                                            v_impl_2793_,
                                        );
                                        v___x_2926_ = v_reuseFailAlloc_2927_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_2785_);
                        leanh::lean_dec(v_k_2784_);
                        if v_isShared_2790_ == 0 {
                            leanh::lean_ctor_set(v___x_2789_, 2, v_v_2781_);
                            leanh::lean_ctor_set(v___x_2789_, 1, v_k_2780_);
                            v___x_2929_ = v___x_2789_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2930_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_size_2783_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2780_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2781_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_l_2786_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_r_2787_);
                            v___x_2929_ = v_reuseFailAlloc_2930_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_size_2783_);
                    v_impl_2931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_2780_, v_v_2781_, v_l_2786_);
                    v___x_2932_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_r_2787_) == 0 {
                        v_size_2933_ = leanh::lean_ctor_get(v_r_2787_, 0);
                        v_size_2934_ = leanh::lean_ctor_get(v_impl_2931_, 0);
                        leanh::lean_inc(v_size_2934_);
                        v_k_2935_ = leanh::lean_ctor_get(v_impl_2931_, 1);
                        leanh::lean_inc(v_k_2935_);
                        v_v_2936_ = leanh::lean_ctor_get(v_impl_2931_, 2);
                        leanh::lean_inc(v_v_2936_);
                        v_l_2937_ = leanh::lean_ctor_get(v_impl_2931_, 3);
                        leanh::lean_inc(v_l_2937_);
                        v_r_2938_ = leanh::lean_ctor_get(v_impl_2931_, 4);
                        leanh::lean_inc(v_r_2938_);
                        v___x_2939_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2940_ = lean_nat_mul(v___x_2939_, v_size_2933_);
                        v___x_2941_ = lean_nat_dec_lt(v___x_2940_, v_size_2934_);
                        leanh::lean_dec(v___x_2940_);
                        if v___x_2941_ == 0 {
                            leanh::lean_dec(v_r_2938_);
                            leanh::lean_dec(v_l_2937_);
                            leanh::lean_dec(v_v_2936_);
                            leanh::lean_dec(v_k_2935_);
                            v___x_2942_ = lean_nat_add(v___x_2932_, v_size_2934_);
                            leanh::lean_dec(v_size_2934_);
                            v___x_2943_ = lean_nat_add(v___x_2942_, v_size_2933_);
                            leanh::lean_dec(v___x_2942_);
                            if v_isShared_2790_ == 0 {
                                leanh::lean_ctor_set(v___x_2789_, 3, v_impl_2931_);
                                leanh::lean_ctor_set(v___x_2789_, 0, v___x_2943_);
                                v___x_2945_ = v___x_2789_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_2946_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_k_2784_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_v_2785_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2946_,
                                    3,
                                    v_impl_2931_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_r_2787_);
                                v___x_2945_ = v_reuseFailAlloc_2946_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3012_ =
                                (!leanh::lean_is_exclusive(v_impl_2931_)) as u8;
                            if v_isSharedCheck_3012_ == 0 {
                                v_unused_3013_ = leanh::lean_ctor_get(v_impl_2931_, 4);
                                leanh::lean_dec(v_unused_3013_);
                                v_unused_3014_ = leanh::lean_ctor_get(v_impl_2931_, 3);
                                leanh::lean_dec(v_unused_3014_);
                                v_unused_3015_ = leanh::lean_ctor_get(v_impl_2931_, 2);
                                leanh::lean_dec(v_unused_3015_);
                                v_unused_3016_ = leanh::lean_ctor_get(v_impl_2931_, 1);
                                leanh::lean_dec(v_unused_3016_);
                                v_unused_3017_ = leanh::lean_ctor_get(v_impl_2931_, 0);
                                leanh::lean_dec(v_unused_3017_);
                                v___x_2948_ = v_impl_2931_;
                                v_isShared_2949_ = v_isSharedCheck_3012_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec(v_impl_2931_);
                                v___x_2948_ = leanh::lean_box(0);
                                v_isShared_2949_ = v_isSharedCheck_3012_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3018_ = leanh::lean_ctor_get(v_impl_2931_, 3);
                        leanh::lean_inc(v_l_3018_);
                        if leanh::lean_obj_tag(v_l_3018_) == 0 {
                            v_r_3019_ = leanh::lean_ctor_get(v_impl_2931_, 4);
                            v_k_3020_ = leanh::lean_ctor_get(v_impl_2931_, 1);
                            v_v_3021_ = leanh::lean_ctor_get(v_impl_2931_, 2);
                            v_isSharedCheck_3032_ =
                                (!leanh::lean_is_exclusive(v_impl_2931_)) as u8;
                            if v_isSharedCheck_3032_ == 0 {
                                v_unused_3033_ = leanh::lean_ctor_get(v_impl_2931_, 3);
                                leanh::lean_dec(v_unused_3033_);
                                v_unused_3034_ = leanh::lean_ctor_get(v_impl_2931_, 0);
                                leanh::lean_dec(v_unused_3034_);
                                v___x_3023_ = v_impl_2931_;
                                v_isShared_3024_ = v_isSharedCheck_3032_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_r_3019_);
                                leanh::lean_inc(v_v_3021_);
                                leanh::lean_inc(v_k_3020_);
                                leanh::lean_dec(v_impl_2931_);
                                v___x_3023_ = leanh::lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3032_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3035_ = leanh::lean_ctor_get(v_impl_2931_, 4);
                            leanh::lean_inc(v_r_3035_);
                            if leanh::lean_obj_tag(v_r_3035_) == 0 {
                                v_k_3036_ = leanh::lean_ctor_get(v_impl_2931_, 1);
                                v_v_3037_ = leanh::lean_ctor_get(v_impl_2931_, 2);
                                v_isSharedCheck_3060_ =
                                    (!leanh::lean_is_exclusive(v_impl_2931_)) as u8;
                                if v_isSharedCheck_3060_ == 0 {
                                    v_unused_3061_ = leanh::lean_ctor_get(v_impl_2931_, 4);
                                    leanh::lean_dec(v_unused_3061_);
                                    v_unused_3062_ = leanh::lean_ctor_get(v_impl_2931_, 3);
                                    leanh::lean_dec(v_unused_3062_);
                                    v_unused_3063_ = leanh::lean_ctor_get(v_impl_2931_, 0);
                                    leanh::lean_dec(v_unused_3063_);
                                    v___x_3039_ = v_impl_2931_;
                                    v_isShared_3040_ = v_isSharedCheck_3060_;
                                    state = 37;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_v_3037_);
                                    leanh::lean_inc(v_k_3036_);
                                    leanh::lean_dec(v_impl_2931_);
                                    v___x_3039_ = leanh::lean_box(0);
                                    v_isShared_3040_ = v_isSharedCheck_3060_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3064_ = leanh::lean_unsigned_to_nat(2);
                                if v_isShared_2790_ == 0 {
                                    leanh::lean_ctor_set(v___x_2789_, 4, v_r_3035_);
                                    leanh::lean_ctor_set(v___x_2789_, 3, v_impl_2931_);
                                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_3064_);
                                    v___x_3066_ = v___x_2789_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3067_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3067_,
                                        0,
                                        v___x_3064_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3067_,
                                        1,
                                        v_k_2784_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3067_,
                                        2,
                                        v_v_2785_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3067_,
                                        3,
                                        v_impl_2931_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3067_,
                                        4,
                                        v_r_3035_,
                                    );
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
                v_size_2812_ = leanh::lean_ctor_get(v_l_2799_, 0);
                v_k_2813_ = leanh::lean_ctor_get(v_l_2799_, 1);
                v_v_2814_ = leanh::lean_ctor_get(v_l_2799_, 2);
                v_l_2815_ = leanh::lean_ctor_get(v_l_2799_, 3);
                v_r_2816_ = leanh::lean_ctor_get(v_l_2799_, 4);
                v_size_2817_ = leanh::lean_ctor_get(v_r_2800_, 0);
                v___x_2818_ = leanh::lean_unsigned_to_nat(2);
                v___x_2819_ = lean_nat_mul(v___x_2818_, v_size_2817_);
                v___x_2820_ = lean_nat_dec_lt(v_size_2812_, v___x_2819_);
                leanh::lean_dec(v___x_2819_);
                if v___x_2820_ == 0 {
                    leanh::lean_inc(v_r_2816_);
                    leanh::lean_inc(v_l_2815_);
                    leanh::lean_inc(v_v_2814_);
                    leanh::lean_inc(v_k_2813_);
                    v_isSharedCheck_2848_ = (!leanh::lean_is_exclusive(v_l_2799_)) as u8;
                    if v_isSharedCheck_2848_ == 0 {
                        v_unused_2849_ = leanh::lean_ctor_get(v_l_2799_, 4);
                        leanh::lean_dec(v_unused_2849_);
                        v_unused_2850_ = leanh::lean_ctor_get(v_l_2799_, 3);
                        leanh::lean_dec(v_unused_2850_);
                        v_unused_2851_ = leanh::lean_ctor_get(v_l_2799_, 2);
                        leanh::lean_dec(v_unused_2851_);
                        v_unused_2852_ = leanh::lean_ctor_get(v_l_2799_, 1);
                        leanh::lean_dec(v_unused_2852_);
                        v_unused_2853_ = leanh::lean_ctor_get(v_l_2799_, 0);
                        leanh::lean_dec(v_unused_2853_);
                        v___x_2822_ = v_l_2799_;
                        v_isShared_2823_ = v_isSharedCheck_2848_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2799_);
                        v___x_2822_ = leanh::lean_box(0);
                        v_isShared_2823_ = v_isSharedCheck_2848_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2789_);
                    v___x_2854_ = lean_nat_add(v___x_2794_, v_size_2795_);
                    v___x_2855_ = lean_nat_add(v___x_2854_, v_size_2796_);
                    leanh::lean_dec(v_size_2796_);
                    v___x_2856_ = lean_nat_add(v___x_2854_, v_size_2812_);
                    leanh::lean_dec(v___x_2854_);
                    leanh::lean_inc_ref(v_l_2786_);
                    if v_isShared_2811_ == 0 {
                        leanh::lean_ctor_set(v___x_2810_, 4, v_l_2799_);
                        leanh::lean_ctor_set(v___x_2810_, 3, v_l_2786_);
                        leanh::lean_ctor_set(v___x_2810_, 2, v_v_2785_);
                        leanh::lean_ctor_set(v___x_2810_, 1, v_k_2784_);
                        leanh::lean_ctor_set(v___x_2810_, 0, v___x_2856_);
                        v___x_2858_ = v___x_2810_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2871_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2856_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2784_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2785_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_l_2786_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_l_2799_);
                        v___x_2858_ = v_reuseFailAlloc_2871_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2824_ = lean_nat_add(v___x_2794_, v_size_2795_);
                v___x_2825_ = lean_nat_add(v___x_2824_, v_size_2796_);
                leanh::lean_dec(v_size_2796_);
                if leanh::lean_obj_tag(v_l_2815_) == 0 {
                    v_size_2846_ = leanh::lean_ctor_get(v_l_2815_, 0);
                    leanh::lean_inc(v_size_2846_);
                    v___y_2838_ = v_size_2846_;
                    state = 8;
                    continue;
                } else {
                    v___x_2847_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2838_ = v___x_2847_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2830_ = lean_nat_add(v___y_2828_, v___y_2829_);
                leanh::lean_dec(v___y_2829_);
                leanh::lean_dec(v___y_2828_);
                if v_isShared_2823_ == 0 {
                    leanh::lean_ctor_set(v___x_2822_, 4, v_r_2800_);
                    leanh::lean_ctor_set(v___x_2822_, 3, v_r_2816_);
                    leanh::lean_ctor_set(v___x_2822_, 2, v_v_2798_);
                    leanh::lean_ctor_set(v___x_2822_, 1, v_k_2797_);
                    leanh::lean_ctor_set(v___x_2822_, 0, v___x_2830_);
                    v___x_2832_ = v___x_2822_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2836_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_k_2797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_v_2798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_r_2816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_r_2800_);
                    v___x_2832_ = v_reuseFailAlloc_2836_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2811_ == 0 {
                    leanh::lean_ctor_set(v___x_2810_, 4, v___x_2832_);
                    leanh::lean_ctor_set(v___x_2810_, 3, v___y_2827_);
                    leanh::lean_ctor_set(v___x_2810_, 2, v_v_2814_);
                    leanh::lean_ctor_set(v___x_2810_, 1, v_k_2813_);
                    leanh::lean_ctor_set(v___x_2810_, 0, v___x_2825_);
                    v___x_2834_ = v___x_2810_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_k_2813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_v_2814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 3, v___y_2827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 4, v___x_2832_);
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
                leanh::lean_dec(v___y_2838_);
                leanh::lean_dec(v___x_2824_);
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v_l_2815_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2789_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_l_2815_);
                    v___x_2841_ = v_reuseFailAlloc_2845_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2842_ = lean_nat_add(v___x_2794_, v_size_2817_);
                if leanh::lean_obj_tag(v_r_2816_) == 0 {
                    v_size_2843_ = leanh::lean_ctor_get(v_r_2816_, 0);
                    leanh::lean_inc(v_size_2843_);
                    v___y_2827_ = v___x_2841_;
                    v___y_2828_ = v___x_2842_;
                    v___y_2829_ = v_size_2843_;
                    state = 5;
                    continue;
                } else {
                    v___x_2844_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2827_ = v___x_2841_;
                    v___y_2828_ = v___x_2842_;
                    v___y_2829_ = v___x_2844_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2865_ = (!leanh::lean_is_exclusive(v_l_2786_)) as u8;
                if v_isSharedCheck_2865_ == 0 {
                    v_unused_2866_ = leanh::lean_ctor_get(v_l_2786_, 4);
                    leanh::lean_dec(v_unused_2866_);
                    v_unused_2867_ = leanh::lean_ctor_get(v_l_2786_, 3);
                    leanh::lean_dec(v_unused_2867_);
                    v_unused_2868_ = leanh::lean_ctor_get(v_l_2786_, 2);
                    leanh::lean_dec(v_unused_2868_);
                    v_unused_2869_ = leanh::lean_ctor_get(v_l_2786_, 1);
                    leanh::lean_dec(v_unused_2869_);
                    v_unused_2870_ = leanh::lean_ctor_get(v_l_2786_, 0);
                    leanh::lean_dec(v_unused_2870_);
                    v___x_2860_ = v_l_2786_;
                    v_isShared_2861_ = v_isSharedCheck_2865_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_l_2786_);
                    v___x_2860_ = leanh::lean_box(0);
                    v_isShared_2861_ = v_isSharedCheck_2865_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2861_ == 0 {
                    leanh::lean_ctor_set(v___x_2860_, 4, v_r_2800_);
                    leanh::lean_ctor_set(v___x_2860_, 3, v___x_2858_);
                    leanh::lean_ctor_set(v___x_2860_, 2, v_v_2798_);
                    leanh::lean_ctor_set(v___x_2860_, 1, v_k_2797_);
                    leanh::lean_ctor_set(v___x_2860_, 0, v___x_2855_);
                    v___x_2863_ = v___x_2860_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_k_2797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_v_2798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 3, v___x_2858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 4, v_r_2800_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2863_;
            }
            13 => {
                v_k_2885_ = leanh::lean_ctor_get(v_l_2878_, 1);
                v_v_2886_ = leanh::lean_ctor_get(v_l_2878_, 2);
                v_isSharedCheck_2900_ = (!leanh::lean_is_exclusive(v_l_2878_)) as u8;
                if v_isSharedCheck_2900_ == 0 {
                    v_unused_2901_ = leanh::lean_ctor_get(v_l_2878_, 4);
                    leanh::lean_dec(v_unused_2901_);
                    v_unused_2902_ = leanh::lean_ctor_get(v_l_2878_, 3);
                    leanh::lean_dec(v_unused_2902_);
                    v_unused_2903_ = leanh::lean_ctor_get(v_l_2878_, 0);
                    leanh::lean_dec(v_unused_2903_);
                    v___x_2888_ = v_l_2878_;
                    v_isShared_2889_ = v_isSharedCheck_2900_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2886_);
                    leanh::lean_inc(v_k_2885_);
                    leanh::lean_dec(v_l_2878_);
                    v___x_2888_ = leanh::lean_box(0);
                    v_isShared_2889_ = v_isSharedCheck_2900_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2890_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_2879_, 2);
                if v_isShared_2889_ == 0 {
                    leanh::lean_ctor_set(v___x_2888_, 4, v_r_2879_);
                    leanh::lean_ctor_set(v___x_2888_, 3, v_r_2879_);
                    leanh::lean_ctor_set(v___x_2888_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v___x_2888_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v___x_2888_, 0, v___x_2794_);
                    v___x_2892_ = v___x_2888_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_r_2879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_r_2879_);
                    v___x_2892_ = v_reuseFailAlloc_2899_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_r_2879_);
                if v_isShared_2884_ == 0 {
                    leanh::lean_ctor_set(v___x_2883_, 3, v_r_2879_);
                    leanh::lean_ctor_set(v___x_2883_, 0, v___x_2794_);
                    v___x_2894_ = v___x_2883_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_k_2880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_v_2881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_r_2879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_r_2879_);
                    v___x_2894_ = v_reuseFailAlloc_2898_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v___x_2894_);
                    leanh::lean_ctor_set(v___x_2789_, 3, v___x_2892_);
                    leanh::lean_ctor_set(v___x_2789_, 2, v_v_2886_);
                    leanh::lean_ctor_set(v___x_2789_, 1, v_k_2885_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2890_);
                    v___x_2896_ = v___x_2789_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2890_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_k_2885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_v_2886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 3, v___x_2892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 4, v___x_2894_);
                    v___x_2896_ = v_reuseFailAlloc_2897_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2896_;
            }
            18 => {
                v___x_2913_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2912_ == 0 {
                    leanh::lean_ctor_set(v___x_2911_, 4, v_l_2878_);
                    leanh::lean_ctor_set(v___x_2911_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v___x_2911_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v___x_2911_, 0, v___x_2794_);
                    v___x_2915_ = v___x_2911_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_l_2878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_l_2878_);
                    v___x_2915_ = v_reuseFailAlloc_2919_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v_r_2907_);
                    leanh::lean_ctor_set(v___x_2789_, 3, v___x_2915_);
                    leanh::lean_ctor_set(v___x_2789_, 2, v_v_2909_);
                    leanh::lean_ctor_set(v___x_2789_, 1, v_k_2908_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2913_);
                    v___x_2917_ = v___x_2789_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_k_2908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_v_2909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 3, v___x_2915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_r_2907_);
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
                v_size_2950_ = leanh::lean_ctor_get(v_l_2937_, 0);
                v_size_2951_ = leanh::lean_ctor_get(v_r_2938_, 0);
                v_k_2952_ = leanh::lean_ctor_get(v_r_2938_, 1);
                v_v_2953_ = leanh::lean_ctor_get(v_r_2938_, 2);
                v_l_2954_ = leanh::lean_ctor_get(v_r_2938_, 3);
                v_r_2955_ = leanh::lean_ctor_get(v_r_2938_, 4);
                v___x_2956_ = leanh::lean_unsigned_to_nat(2);
                v___x_2957_ = lean_nat_mul(v___x_2956_, v_size_2950_);
                v___x_2958_ = lean_nat_dec_lt(v_size_2951_, v___x_2957_);
                leanh::lean_dec(v___x_2957_);
                if v___x_2958_ == 0 {
                    leanh::lean_inc(v_r_2955_);
                    leanh::lean_inc(v_l_2954_);
                    leanh::lean_inc(v_v_2953_);
                    leanh::lean_inc(v_k_2952_);
                    v_isSharedCheck_2987_ = (!leanh::lean_is_exclusive(v_r_2938_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v_unused_2988_ = leanh::lean_ctor_get(v_r_2938_, 4);
                        leanh::lean_dec(v_unused_2988_);
                        v_unused_2989_ = leanh::lean_ctor_get(v_r_2938_, 3);
                        leanh::lean_dec(v_unused_2989_);
                        v_unused_2990_ = leanh::lean_ctor_get(v_r_2938_, 2);
                        leanh::lean_dec(v_unused_2990_);
                        v_unused_2991_ = leanh::lean_ctor_get(v_r_2938_, 1);
                        leanh::lean_dec(v_unused_2991_);
                        v_unused_2992_ = leanh::lean_ctor_get(v_r_2938_, 0);
                        leanh::lean_dec(v_unused_2992_);
                        v___x_2960_ = v_r_2938_;
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2938_);
                        v___x_2960_ = leanh::lean_box(0);
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2789_);
                    v___x_2993_ = lean_nat_add(v___x_2932_, v_size_2934_);
                    leanh::lean_dec(v_size_2934_);
                    v___x_2994_ = lean_nat_add(v___x_2993_, v_size_2933_);
                    leanh::lean_dec(v___x_2993_);
                    v___x_2995_ = lean_nat_add(v___x_2932_, v_size_2933_);
                    v___x_2996_ = lean_nat_add(v___x_2995_, v_size_2951_);
                    leanh::lean_dec(v___x_2995_);
                    leanh::lean_inc_ref(v_r_2787_);
                    if v_isShared_2949_ == 0 {
                        leanh::lean_ctor_set(v___x_2948_, 4, v_r_2787_);
                        leanh::lean_ctor_set(v___x_2948_, 3, v_r_2938_);
                        leanh::lean_ctor_set(v___x_2948_, 2, v_v_2785_);
                        leanh::lean_ctor_set(v___x_2948_, 1, v_k_2784_);
                        leanh::lean_ctor_set(v___x_2948_, 0, v___x_2996_);
                        v___x_2998_ = v___x_2948_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3011_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2996_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2784_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_2785_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_r_2938_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_r_2787_);
                        v___x_2998_ = v_reuseFailAlloc_3011_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2962_ = lean_nat_add(v___x_2932_, v_size_2934_);
                leanh::lean_dec(v_size_2934_);
                v___x_2963_ = lean_nat_add(v___x_2962_, v_size_2933_);
                leanh::lean_dec(v___x_2962_);
                v___x_2975_ = lean_nat_add(v___x_2932_, v_size_2950_);
                if leanh::lean_obj_tag(v_l_2954_) == 0 {
                    v_size_2985_ = leanh::lean_ctor_get(v_l_2954_, 0);
                    leanh::lean_inc(v_size_2985_);
                    v___y_2977_ = v_size_2985_;
                    state = 29;
                    continue;
                } else {
                    v___x_2986_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2977_ = v___x_2986_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2968_ = lean_nat_add(v___y_2965_, v___y_2967_);
                leanh::lean_dec(v___y_2967_);
                leanh::lean_dec(v___y_2965_);
                if v_isShared_2961_ == 0 {
                    leanh::lean_ctor_set(v___x_2960_, 4, v_r_2787_);
                    leanh::lean_ctor_set(v___x_2960_, 3, v_r_2955_);
                    leanh::lean_ctor_set(v___x_2960_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v___x_2960_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v___x_2960_, 0, v___x_2968_);
                    v___x_2970_ = v___x_2960_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_r_2955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_r_2787_);
                    v___x_2970_ = v_reuseFailAlloc_2974_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2949_ == 0 {
                    leanh::lean_ctor_set(v___x_2948_, 4, v___x_2970_);
                    leanh::lean_ctor_set(v___x_2948_, 3, v___y_2966_);
                    leanh::lean_ctor_set(v___x_2948_, 2, v_v_2953_);
                    leanh::lean_ctor_set(v___x_2948_, 1, v_k_2952_);
                    leanh::lean_ctor_set(v___x_2948_, 0, v___x_2963_);
                    v___x_2972_ = v___x_2948_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_k_2952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_v_2953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___y_2966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___x_2970_);
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
                leanh::lean_dec(v___y_2977_);
                leanh::lean_dec(v___x_2975_);
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v_l_2954_);
                    leanh::lean_ctor_set(v___x_2789_, 3, v_l_2937_);
                    leanh::lean_ctor_set(v___x_2789_, 2, v_v_2936_);
                    leanh::lean_ctor_set(v___x_2789_, 1, v_k_2935_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2978_);
                    v___x_2980_ = v___x_2789_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_k_2935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_v_2936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_l_2937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_l_2954_);
                    v___x_2980_ = v_reuseFailAlloc_2984_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2981_ = lean_nat_add(v___x_2932_, v_size_2933_);
                if leanh::lean_obj_tag(v_r_2955_) == 0 {
                    v_size_2982_ = leanh::lean_ctor_get(v_r_2955_, 0);
                    leanh::lean_inc(v_size_2982_);
                    v___y_2965_ = v___x_2981_;
                    v___y_2966_ = v___x_2980_;
                    v___y_2967_ = v_size_2982_;
                    state = 26;
                    continue;
                } else {
                    v___x_2983_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2965_ = v___x_2981_;
                    v___y_2966_ = v___x_2980_;
                    v___y_2967_ = v___x_2983_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3005_ = (!leanh::lean_is_exclusive(v_r_2787_)) as u8;
                if v_isSharedCheck_3005_ == 0 {
                    v_unused_3006_ = leanh::lean_ctor_get(v_r_2787_, 4);
                    leanh::lean_dec(v_unused_3006_);
                    v_unused_3007_ = leanh::lean_ctor_get(v_r_2787_, 3);
                    leanh::lean_dec(v_unused_3007_);
                    v_unused_3008_ = leanh::lean_ctor_get(v_r_2787_, 2);
                    leanh::lean_dec(v_unused_3008_);
                    v_unused_3009_ = leanh::lean_ctor_get(v_r_2787_, 1);
                    leanh::lean_dec(v_unused_3009_);
                    v_unused_3010_ = leanh::lean_ctor_get(v_r_2787_, 0);
                    leanh::lean_dec(v_unused_3010_);
                    v___x_3000_ = v_r_2787_;
                    v_isShared_3001_ = v_isSharedCheck_3005_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_r_2787_);
                    v___x_3000_ = leanh::lean_box(0);
                    v_isShared_3001_ = v_isSharedCheck_3005_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3001_ == 0 {
                    leanh::lean_ctor_set(v___x_3000_, 4, v___x_2998_);
                    leanh::lean_ctor_set(v___x_3000_, 3, v_l_2937_);
                    leanh::lean_ctor_set(v___x_3000_, 2, v_v_2936_);
                    leanh::lean_ctor_set(v___x_3000_, 1, v_k_2935_);
                    leanh::lean_ctor_set(v___x_3000_, 0, v___x_2994_);
                    v___x_3003_ = v___x_3000_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_k_2935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_v_2936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_l_2937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 4, v___x_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3003_;
            }
            34 => {
                v___x_3025_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_3019_);
                if v_isShared_3024_ == 0 {
                    leanh::lean_ctor_set(v___x_3023_, 3, v_r_3019_);
                    leanh::lean_ctor_set(v___x_3023_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v___x_3023_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v___x_3023_, 0, v___x_2932_);
                    v___x_3027_ = v___x_3023_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_2932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_r_3019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 4, v_r_3019_);
                    v___x_3027_ = v_reuseFailAlloc_3031_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v___x_3027_);
                    leanh::lean_ctor_set(v___x_2789_, 3, v_l_3018_);
                    leanh::lean_ctor_set(v___x_2789_, 2, v_v_3021_);
                    leanh::lean_ctor_set(v___x_2789_, 1, v_k_3020_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_3025_);
                    v___x_3029_ = v___x_2789_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_k_3020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_v_3021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_l_3018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 4, v___x_3027_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3029_;
            }
            37 => {
                v_k_3041_ = leanh::lean_ctor_get(v_r_3035_, 1);
                v_v_3042_ = leanh::lean_ctor_get(v_r_3035_, 2);
                v_isSharedCheck_3056_ = (!leanh::lean_is_exclusive(v_r_3035_)) as u8;
                if v_isSharedCheck_3056_ == 0 {
                    v_unused_3057_ = leanh::lean_ctor_get(v_r_3035_, 4);
                    leanh::lean_dec(v_unused_3057_);
                    v_unused_3058_ = leanh::lean_ctor_get(v_r_3035_, 3);
                    leanh::lean_dec(v_unused_3058_);
                    v_unused_3059_ = leanh::lean_ctor_get(v_r_3035_, 0);
                    leanh::lean_dec(v_unused_3059_);
                    v___x_3044_ = v_r_3035_;
                    v_isShared_3045_ = v_isSharedCheck_3056_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3042_);
                    leanh::lean_inc(v_k_3041_);
                    leanh::lean_dec(v_r_3035_);
                    v___x_3044_ = leanh::lean_box(0);
                    v_isShared_3045_ = v_isSharedCheck_3056_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3046_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3045_ == 0 {
                    leanh::lean_ctor_set(v___x_3044_, 4, v_l_3018_);
                    leanh::lean_ctor_set(v___x_3044_, 3, v_l_3018_);
                    leanh::lean_ctor_set(v___x_3044_, 2, v_v_3037_);
                    leanh::lean_ctor_set(v___x_3044_, 1, v_k_3036_);
                    leanh::lean_ctor_set(v___x_3044_, 0, v___x_2932_);
                    v___x_3048_ = v___x_3044_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_2932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_3036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_3037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_l_3018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_l_3018_);
                    v___x_3048_ = v_reuseFailAlloc_3055_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3040_ == 0 {
                    leanh::lean_ctor_set(v___x_3039_, 4, v_l_3018_);
                    leanh::lean_ctor_set(v___x_3039_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v___x_3039_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v___x_3039_, 0, v___x_2932_);
                    v___x_3050_ = v___x_3039_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_2932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_k_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_v_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_l_3018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_l_3018_);
                    v___x_3050_ = v_reuseFailAlloc_3054_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 4, v___x_3050_);
                    leanh::lean_ctor_set(v___x_2789_, 3, v___x_3048_);
                    leanh::lean_ctor_set(v___x_2789_, 2, v_v_3042_);
                    leanh::lean_ctor_set(v___x_2789_, 1, v_k_3041_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_3046_);
                    v___x_3052_ = v___x_2789_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3046_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_k_3041_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_v_3042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 3, v___x_3048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 4, v___x_3050_);
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
    mut v_overlapping_3071_: *mut leanh::LeanObject,
    mut v_s_x3f_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_s_x3f_3072_) == 0 {
                    v___x_3080_ = leanh::lean_box(1);
                    v___y_3074_ = v___x_3080_;
                    state = 1;
                    continue;
                } else {
                    v_val_3081_ = leanh::lean_ctor_get(v_s_x3f_3072_, 0);
                    leanh::lean_inc(v_val_3081_);
                    leanh::lean_dec_ref_known(v_s_x3f_3072_, 1);
                    v___y_3074_ = v_val_3081_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3075_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_3071_, v___y_3074_);
                if v___x_3075_ == 0 {
                    v___x_3076_ = leanh::lean_box(0);
                    v___x_3077_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_3071_, v___x_3076_, v___y_3074_);
                    v___x_3078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3078_, 0, v___x_3077_);
                    return v___x_3078_;
                } else {
                    leanh::lean_dec(v_overlapping_3071_);
                    v___x_3079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3079_, 0, v___y_3074_);
                    return v___x_3079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(
    mut v_overlapping_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_x_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v_tail_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3084_) == 0 {
                    v___x_3085_ = leanh::lean_box(0);
                    v___x_3086_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_3082_, v___x_3085_);
                    v_val_3087_ = leanh::lean_ctor_get(v___x_3086_, 0);
                    leanh::lean_inc(v_val_3087_);
                    leanh::lean_dec(v___x_3086_);
                    v___x_3088_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3088_, 0, v_a_3083_);
                    leanh::lean_ctor_set(v___x_3088_, 1, v_val_3087_);
                    leanh::lean_ctor_set(v___x_3088_, 2, v_x_3084_);
                    return v___x_3088_;
                } else {
                    v_key_3089_ = leanh::lean_ctor_get(v_x_3084_, 0);
                    v_value_3090_ = leanh::lean_ctor_get(v_x_3084_, 1);
                    v_tail_3091_ = leanh::lean_ctor_get(v_x_3084_, 2);
                    v_isSharedCheck_3106_ = (!leanh::lean_is_exclusive(v_x_3084_)) as u8;
                    if v_isSharedCheck_3106_ == 0 {
                        v___x_3093_ = v_x_3084_;
                        v_isShared_3094_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3091_);
                        leanh::lean_inc(v_value_3090_);
                        leanh::lean_inc(v_key_3089_);
                        leanh::lean_dec(v_x_3084_);
                        v___x_3093_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_3093_, 2, v_tail_3096_);
                        v___x_3098_ = v___x_3093_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3099_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_key_3089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_value_3090_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_tail_3096_);
                        v___x_3098_ = v_reuseFailAlloc_3099_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_3089_);
                    v___x_3100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3100_, 0, v_value_3090_);
                    v___x_3101_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_3082_, v___x_3100_);
                    v_val_3102_ = leanh::lean_ctor_get(v___x_3101_, 0);
                    leanh::lean_inc(v_val_3102_);
                    leanh::lean_dec(v___x_3101_);
                    if v_isShared_3094_ == 0 {
                        leanh::lean_ctor_set(v___x_3093_, 1, v_val_3102_);
                        leanh::lean_ctor_set(v___x_3093_, 0, v_a_3083_);
                        v___x_3104_ = v___x_3093_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3105_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3083_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_val_3102_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_tail_3091_);
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
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_x_3108_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3109_: u8 = 0;
    let mut v_key_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3108_) == 0 {
                    v___x_3109_ = 0;
                    return v___x_3109_;
                } else {
                    v_key_3110_ = leanh::lean_ctor_get(v_x_3108_, 0);
                    v_tail_3111_ = leanh::lean_ctor_get(v_x_3108_, 2);
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
    mut v_a_3114_: *mut leanh::LeanObject,
    mut v_x_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3116_: u8 = 0;
    let mut v_r_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3114_, v_x_3115_);
    leanh::lean_dec(v_x_3115_);
    leanh::lean_dec(v_a_3114_);
    v_r_3117_ = leanh::lean_box((v_res_3116_) as usize);
    return v_r_3117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_x_3118_: *mut leanh::LeanObject,
    mut v_x_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3119_) == 0 {
                    return v_x_3118_;
                } else {
                    v_key_3120_ = leanh::lean_ctor_get(v_x_3119_, 0);
                    v_value_3121_ = leanh::lean_ctor_get(v_x_3119_, 1);
                    v_tail_3122_ = leanh::lean_ctor_get(v_x_3119_, 2);
                    v_isSharedCheck_3145_ = (!leanh::lean_is_exclusive(v_x_3119_)) as u8;
                    if v_isSharedCheck_3145_ == 0 {
                        v___x_3124_ = v_x_3119_;
                        v_isShared_3125_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3122_);
                        leanh::lean_inc(v_value_3121_);
                        leanh::lean_inc(v_key_3120_);
                        leanh::lean_dec(v_x_3119_);
                        v___x_3124_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_3139_);
                if v_isShared_3125_ == 0 {
                    leanh::lean_ctor_set(v___x_3124_, 2, v___x_3139_);
                    v___x_3141_ = v___x_3124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3144_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_key_3120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_value_3121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3139_);
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
    mut v_i_3146_: *mut leanh::LeanObject,
    mut v_source_3147_: *mut leanh::LeanObject,
    mut v_target_3148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v_es_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3149_ = lean_array_get_size(v_source_3147_);
                v___x_3150_ = lean_nat_dec_lt(v_i_3146_, v___x_3149_);
                if v___x_3150_ == 0 {
                    leanh::lean_dec_ref(v_source_3147_);
                    leanh::lean_dec(v_i_3146_);
                    return v_target_3148_;
                } else {
                    v_es_3151_ = lean_array_fget(v_source_3147_, v_i_3146_);
                    v___x_3152_ = leanh::lean_box(0);
                    v_source_3153_ = lean_array_fset(v_source_3147_, v_i_3146_, v___x_3152_);
                    v_target_3154_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_target_3148_, v_es_3151_);
                    v___x_3155_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3156_ = lean_nat_add(v_i_3146_, v___x_3155_);
                    leanh::lean_dec(v_i_3146_);
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
    mut v_data_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ = lean_array_get_size(v_data_3158_);
    v___x_3160_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3161_ = lean_nat_mul(v___x_3159_, v___x_3160_);
    v___x_3162_ = leanh::lean_unsigned_to_nat(0);
    v___x_3163_ = leanh::lean_box(0);
    v___x_3164_ = lean_mk_array(v_nbuckets_3161_, v___x_3163_);
    v___x_3165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v___x_3162_, v_data_3158_, v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(
    mut v_overlapping_3166_: *mut leanh::LeanObject,
    mut v_m_3167_: *mut leanh::LeanObject,
    mut v_a_3168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v_val_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3169_ = leanh::lean_ctor_get(v_m_3167_, 0);
                v_buckets_3170_ = leanh::lean_ctor_get(v_m_3167_, 1);
                v_isSharedCheck_3222_ = (!leanh::lean_is_exclusive(v_m_3167_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3172_ = v_m_3167_;
                    v_isShared_3173_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3170_);
                    leanh::lean_inc(v_size_3169_);
                    leanh::lean_dec(v_m_3167_);
                    v___x_3172_ = leanh::lean_box(0);
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
                    v___x_3208_ = leanh::lean_box(1);
                    v___x_3209_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_3166_, v___x_3208_);
                    if v___x_3209_ == 0 {
                        v___x_3210_ = leanh::lean_box(0);
                        v___x_3211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_3166_, v___x_3210_, v___x_3208_);
                        v___y_3189_ = v___x_3211_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_overlapping_3166_);
                        v___y_3189_ = v___x_3208_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_bkt_3187_);
                    leanh::lean_del_object(v___x_3172_);
                    v___x_3212_ = leanh::lean_box(0);
                    v_buckets_x27_3213_ =
                        lean_array_uset(v_buckets_3170_, v___x_3186_, v___x_3212_);
                    leanh::lean_inc(v_a_3168_);
                    v_bkt_x27_3214_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_3166_, v_a_3168_, v_bkt_3187_);
                    v___x_3219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3168_, v_bkt_x27_3214_);
                    leanh::lean_dec(v_a_3168_);
                    if v___x_3219_ == 0 {
                        v___x_3220_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3221_ = lean_nat_sub(v_size_3169_, v___x_3220_);
                        leanh::lean_dec(v_size_3169_);
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
                v___x_3190_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3191_ = lean_nat_add(v_size_3169_, v___x_3190_);
                leanh::lean_dec(v_size_3169_);
                leanh::lean_inc(v_bkt_3187_);
                v___x_3192_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3192_, 0, v_a_3168_);
                leanh::lean_ctor_set(v___x_3192_, 1, v___y_3189_);
                leanh::lean_ctor_set(v___x_3192_, 2, v_bkt_3187_);
                v_buckets_x27_3193_ = lean_array_uset(v_buckets_3170_, v___x_3186_, v___x_3192_);
                v___x_3194_ = leanh::lean_unsigned_to_nat(4);
                v___x_3195_ = lean_nat_mul(v_size_x27_3191_, v___x_3194_);
                v___x_3196_ = leanh::lean_unsigned_to_nat(3);
                v___x_3197_ = lean_nat_div(v___x_3195_, v___x_3196_);
                leanh::lean_dec(v___x_3195_);
                v___x_3198_ = lean_array_get_size(v_buckets_x27_3193_);
                v___x_3199_ = lean_nat_dec_le(v___x_3197_, v___x_3198_);
                leanh::lean_dec(v___x_3197_);
                if v___x_3199_ == 0 {
                    v_val_3200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_buckets_x27_3193_);
                    if v_isShared_3173_ == 0 {
                        leanh::lean_ctor_set(v___x_3172_, 1, v_val_3200_);
                        leanh::lean_ctor_set(v___x_3172_, 0, v_size_x27_3191_);
                        v___x_3202_ = v___x_3172_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_size_x27_3191_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_val_3200_);
                        v___x_3202_ = v_reuseFailAlloc_3203_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3173_ == 0 {
                        leanh::lean_ctor_set(v___x_3172_, 1, v_buckets_x27_3193_);
                        leanh::lean_ctor_set(v___x_3172_, 0, v_size_x27_3191_);
                        v___x_3205_ = v___x_3172_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_size_x27_3191_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_buckets_x27_3193_);
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
                v___x_3218_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3218_, 0, v___y_3216_);
                leanh::lean_ctor_set(v___x_3218_, 1, v___x_3217_);
                return v___x_3218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_insert(
    mut v_o_3223_: *mut leanh::LeanObject,
    mut v_overlapping_3224_: *mut leanh::LeanObject,
    mut v_overlapped_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_overlapping_3224_, v_o_3223_, v_overlapped_3225_);
    return v___x_3226_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(
    mut v_00_u03b2_3227_: *mut leanh::LeanObject,
    mut v_k_3228_: *mut leanh::LeanObject,
    mut v_t_3229_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3230_: u8 = 0;
    v___x_3230_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_3228_, v_t_3229_);
    return v___x_3230_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(
    mut v_00_u03b2_3231_: *mut leanh::LeanObject,
    mut v_k_3232_: *mut leanh::LeanObject,
    mut v_t_3233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3234_: u8 = 0;
    let mut v_r_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3234_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(
            v_00_u03b2_3231_,
            v_k_3232_,
            v_t_3233_,
        );
    leanh::lean_dec(v_t_3233_);
    leanh::lean_dec(v_k_3232_);
    v_r_3235_ = leanh::lean_box((v_res_3234_) as usize);
    return v_r_3235_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(
    mut v_00_u03b2_3236_: *mut leanh::LeanObject,
    mut v_k_3237_: *mut leanh::LeanObject,
    mut v_v_3238_: *mut leanh::LeanObject,
    mut v_t_3239_: *mut leanh::LeanObject,
    mut v_hl_3240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_3237_, v_v_3238_, v_t_3239_);
    return v___x_3241_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(
    mut v_00_u03b2_3242_: *mut leanh::LeanObject,
    mut v_a_3243_: *mut leanh::LeanObject,
    mut v_x_3244_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3245_: u8 = 0;
    v___x_3245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_3243_, v_x_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(
    mut v_00_u03b2_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_x_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3249_: u8 = 0;
    let mut v_r_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_3246_, v_a_3247_, v_x_3248_);
    leanh::lean_dec(v_x_3248_);
    leanh::lean_dec(v_a_3247_);
    v_r_3250_ = leanh::lean_box((v_res_3249_) as usize);
    return v_r_3250_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(
    mut v_00_u03b2_3251_: *mut leanh::LeanObject,
    mut v_data_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_data_3252_);
    return v___x_3253_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3254_: *mut leanh::LeanObject,
    mut v_i_3255_: *mut leanh::LeanObject,
    mut v_source_3256_: *mut leanh::LeanObject,
    mut v_target_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v_i_3255_, v_source_3256_, v_target_3257_);
    return v___x_3258_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3259_: *mut leanh::LeanObject,
    mut v_x_3260_: *mut leanh::LeanObject,
    mut v_x_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_x_3260_, v_x_3261_);
    return v___x_3262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(
    mut v_a_3263_: *mut leanh::LeanObject,
    mut v_x_3264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3264_) == 0 {
                    v___x_3265_ = leanh::lean_box(0);
                    return v___x_3265_;
                } else {
                    v_key_3266_ = leanh::lean_ctor_get(v_x_3264_, 0);
                    v_value_3267_ = leanh::lean_ctor_get(v_x_3264_, 1);
                    v_tail_3268_ = leanh::lean_ctor_get(v_x_3264_, 2);
                    v___x_3269_ = lean_nat_dec_eq(v_key_3266_, v_a_3263_);
                    if v___x_3269_ == 0 {
                        v_x_3264_ = v_tail_3268_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3267_);
                        v___x_3271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3271_, 0, v_value_3267_);
                        return v___x_3271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(
    mut v_a_3272_: *mut leanh::LeanObject,
    mut v_x_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_3272_, v_x_3273_);
    leanh::lean_dec(v_x_3273_);
    leanh::lean_dec(v_a_3272_);
    return v_res_3274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(
    mut v_m_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3277_ = leanh::lean_ctor_get(v_m_3275_, 1);
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
    mut v_m_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_3293_, v_a_3294_);
    leanh::lean_dec(v_a_3294_);
    leanh::lean_dec_ref(v_m_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(
    mut v_init_3296_: *mut leanh::LeanObject,
    mut v_x_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3297_) == 0 {
                    v_k_3298_ = leanh::lean_ctor_get(v_x_3297_, 1);
                    leanh::lean_inc(v_k_3298_);
                    v_l_3299_ = leanh::lean_ctor_get(v_x_3297_, 3);
                    leanh::lean_inc(v_l_3299_);
                    v_r_3300_ = leanh::lean_ctor_get(v_x_3297_, 4);
                    leanh::lean_inc(v_r_3300_);
                    leanh::lean_dec_ref_known(v_x_3297_, 5);
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
    mut v_o_3306_: *mut leanh::LeanObject,
    mut v_overlapped_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_3306_, v_overlapped_3307_);
                if leanh::lean_obj_tag(v___x_3308_) == 0 {
                    v___x_3309_ = l_Lean_Meta_Match_Overlaps_overlapping___closed__0;
                    return v___x_3309_;
                } else {
                    v_val_3310_ = leanh::lean_ctor_get(v___x_3308_, 0);
                    leanh::lean_inc(v_val_3310_);
                    leanh::lean_dec_ref_known(v___x_3308_, 1);
                    if leanh::lean_obj_tag(v_val_3310_) == 0 {
                        v_size_3315_ = leanh::lean_ctor_get(v_val_3310_, 0);
                        leanh::lean_inc(v_size_3315_);
                        v___y_3312_ = v_size_3315_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3316_ = leanh::lean_unsigned_to_nat(0);
                        v___y_3312_ = v___x_3316_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3313_ = lean_mk_empty_array_with_capacity(v___y_3312_);
                leanh::lean_dec(v___y_3312_);
                v___x_3314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_3313_, v_val_3310_);
                return v___x_3314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Overlaps_overlapping___boxed(
    mut v_o_3317_: *mut leanh::LeanObject,
    mut v_overlapped_3318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_3317_, v_overlapped_3318_);
    leanh::lean_dec(v_overlapped_3318_);
    leanh::lean_dec_ref(v_o_3317_);
    return v_res_3319_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(
    mut v_00_u03b2_3320_: *mut leanh::LeanObject,
    mut v_m_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_3321_, v_a_3322_);
    return v___x_3323_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(
    mut v_00_u03b2_3324_: *mut leanh::LeanObject,
    mut v_m_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_3324_, v_m_3325_, v_a_3326_);
    leanh::lean_dec(v_a_3326_);
    leanh::lean_dec_ref(v_m_3325_);
    return v_res_3327_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(
    mut v_init_3328_: *mut leanh::LeanObject,
    mut v_t_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_3328_, v_t_3329_);
    return v___x_3330_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(
    mut v_00_u03b2_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_x_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3334_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_3332_, v_x_3333_);
    return v___x_3334_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(
    mut v_00_u03b2_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
    mut v_x_3337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_3335_, v_a_3336_, v_x_3337_);
    leanh::lean_dec(v_x_3337_);
    leanh::lean_dec(v_a_3336_);
    return v_res_3338_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = leanh::lean_unsigned_to_nat(13);
    v___x_3354_ = lean_nat_to_int(v___x_3353_);
    return v___x_3354_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = leanh::lean_unsigned_to_nat(15);
    v___x_3359_ = lean_nat_to_int(v___x_3358_);
    return v___x_3359_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = leanh::lean_unsigned_to_nat(16);
    v___x_3364_ = lean_nat_to_int(v___x_3363_);
    return v___x_3364_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(
    mut v_x_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numFields_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3368_: u8 = 0;
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numFields_3366_ = leanh::lean_ctor_get(v_x_3365_, 0);
    leanh::lean_inc(v_numFields_3366_);
    v_numOverlaps_3367_ = leanh::lean_ctor_get(v_x_3365_, 1);
    leanh::lean_inc(v_numOverlaps_3367_);
    v_hasUnitThunk_3368_ = leanh::lean_ctor_get_uint8(
        v_x_3365_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    leanh::lean_dec_ref(v_x_3365_);
    v___x_3369_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5;
    v___x_3370_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3;
    v___x_3371_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4,
    );
    v___x_3372_ = l_Nat_reprFast(v_numFields_3366_);
    v___x_3373_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3373_, 0, v___x_3372_);
    v___x_3374_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3374_, 0, v___x_3371_);
    leanh::lean_ctor_set(v___x_3374_, 1, v___x_3373_);
    v___x_3375_ = 0;
    v___x_3376_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3376_, 0, v___x_3374_);
    leanh::lean_ctor_set_uint8(
        v___x_3376_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3377_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3377_, 0, v___x_3370_);
    leanh::lean_ctor_set(v___x_3377_, 1, v___x_3376_);
    v___x_3378_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4;
    v___x_3379_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3379_, 0, v___x_3377_);
    leanh::lean_ctor_set(v___x_3379_, 1, v___x_3378_);
    v___x_3380_ = leanh::lean_box(1);
    v___x_3381_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3381_, 0, v___x_3379_);
    leanh::lean_ctor_set(v___x_3381_, 1, v___x_3380_);
    v___x_3382_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6;
    v___x_3383_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3383_, 0, v___x_3381_);
    leanh::lean_ctor_set(v___x_3383_, 1, v___x_3382_);
    v___x_3384_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3384_, 0, v___x_3383_);
    leanh::lean_ctor_set(v___x_3384_, 1, v___x_3369_);
    v___x_3385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7,
    );
    v___x_3386_ = l_Nat_reprFast(v_numOverlaps_3367_);
    v___x_3387_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3387_, 0, v___x_3386_);
    v___x_3388_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3388_, 0, v___x_3385_);
    leanh::lean_ctor_set(v___x_3388_, 1, v___x_3387_);
    v___x_3389_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3388_);
    leanh::lean_ctor_set_uint8(
        v___x_3389_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3390_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3390_, 0, v___x_3384_);
    leanh::lean_ctor_set(v___x_3390_, 1, v___x_3389_);
    v___x_3391_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3390_);
    leanh::lean_ctor_set(v___x_3391_, 1, v___x_3378_);
    v___x_3392_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3392_, 0, v___x_3391_);
    leanh::lean_ctor_set(v___x_3392_, 1, v___x_3380_);
    v___x_3393_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9;
    v___x_3394_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3394_, 0, v___x_3392_);
    leanh::lean_ctor_set(v___x_3394_, 1, v___x_3393_);
    v___x_3395_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3395_, 0, v___x_3394_);
    leanh::lean_ctor_set(v___x_3395_, 1, v___x_3369_);
    v___x_3396_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10,
    );
    v___x_3397_ = l_Bool_repr___redArg(v_hasUnitThunk_3368_);
    v___x_3398_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3398_, 0, v___x_3396_);
    leanh::lean_ctor_set(v___x_3398_, 1, v___x_3397_);
    v___x_3399_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    leanh::lean_ctor_set_uint8(
        v___x_3399_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    v___x_3400_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3400_, 0, v___x_3395_);
    leanh::lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    v___x_3401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_3402_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_3403_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3403_, 0, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 1, v___x_3400_);
    v___x_3404_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_3405_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3403_);
    leanh::lean_ctor_set(v___x_3405_, 1, v___x_3404_);
    v___x_3406_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3406_, 0, v___x_3401_);
    leanh::lean_ctor_set(v___x_3406_, 1, v___x_3405_);
    v___x_3407_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3407_, 0, v___x_3406_);
    leanh::lean_ctor_set_uint8(
        v___x_3407_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr(
    mut v_x_3408_: *mut leanh::LeanObject,
    mut v_prec_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_3408_);
    return v___x_3410_;
}
pub unsafe fn l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(
    mut v_x_3411_: *mut leanh::LeanObject,
    mut v_prec_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_3411_, v_prec_3412_);
    leanh::lean_dec(v_prec_3412_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_Meta_Match_instBEqAltParamInfo_beq(
    mut v_x_3416_: *mut leanh::LeanObject,
    mut v_x_3417_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_numFields_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3420_: u8 = 0;
    let mut v_numFields_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    v_numFields_3418_ = leanh::lean_ctor_get(v_x_3416_, 0);
    v_numOverlaps_3419_ = leanh::lean_ctor_get(v_x_3416_, 1);
    v_hasUnitThunk_3420_ = leanh::lean_ctor_get_uint8(
        v_x_3416_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_numFields_3421_ = leanh::lean_ctor_get(v_x_3417_, 0);
    v_numOverlaps_3422_ = leanh::lean_ctor_get(v_x_3417_, 1);
    v_hasUnitThunk_3423_ = leanh::lean_ctor_get_uint8(
        v_x_3417_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_3426_: *mut leanh::LeanObject,
    mut v_x_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3428_: u8 = 0;
    let mut v_r_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_3426_, v_x_3427_);
    leanh::lean_dec_ref(v_x_3427_);
    leanh::lean_dec_ref(v_x_3426_);
    v_r_3429_ = leanh::lean_box((v_res_3428_) as usize);
    return v_r_3429_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
    v___x_3435_ = leanh::lean_box(0);
    v___x_3436_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0;
    v___x_3437_ = leanh::lean_unsigned_to_nat(0);
    v___x_3438_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3438_, 0, v___x_3437_);
    leanh::lean_ctor_set(v___x_3438_, 1, v___x_3437_);
    leanh::lean_ctor_set(v___x_3438_, 2, v___x_3436_);
    leanh::lean_ctor_set(v___x_3438_, 3, v___x_3435_);
    leanh::lean_ctor_set(v___x_3438_, 4, v___x_3436_);
    leanh::lean_ctor_set(v___x_3438_, 5, v___x_3434_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1,
    );
    return v___x_3439_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatcherInfo() -> *mut leanh::LeanObject {
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
    return v___x_3440_;
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
    mut v_x_3441_: *mut leanh::LeanObject,
    mut v_x_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3441_) == 0 {
                    v___x_3443_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1;
                    return v___x_3443_;
                } else {
                    v_val_3444_ = leanh::lean_ctor_get(v_x_3441_, 0);
                    v_isSharedCheck_3455_ = (!leanh::lean_is_exclusive(v_x_3441_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3446_ = v_x_3441_;
                        v_isShared_3447_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3444_);
                        leanh::lean_dec(v_x_3441_);
                        v___x_3446_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set_tag(v___x_3446_, 3);
                    leanh::lean_ctor_set(v___x_3446_, 0, v___x_3449_);
                    v___x_3451_ = v___x_3446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3449_);
                    v___x_3451_ = v_reuseFailAlloc_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3452_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3452_, 0, v___x_3448_);
                leanh::lean_ctor_set(v___x_3452_, 1, v___x_3451_);
                v___x_3453_ = l_Repr_addAppParen(v___x_3452_, v_x_3442_);
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(
    mut v_x_3456_: *mut leanh::LeanObject,
    mut v_x_3457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
        v_x_3456_, v_x_3457_,
    );
    leanh::lean_dec(v_x_3457_);
    return v_res_3458_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_x_3459_: *mut leanh::LeanObject,
    mut v_x_3460_: *mut leanh::LeanObject,
    mut v_x_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3461_) == 0 {
                    leanh::lean_dec(v_x_3459_);
                    return v_x_3460_;
                } else {
                    v_head_3462_ = leanh::lean_ctor_get(v_x_3461_, 0);
                    v_tail_3463_ = leanh::lean_ctor_get(v_x_3461_, 1);
                    v_isSharedCheck_3473_ = (!leanh::lean_is_exclusive(v_x_3461_)) as u8;
                    if v_isSharedCheck_3473_ == 0 {
                        v___x_3465_ = v_x_3461_;
                        v_isShared_3466_ = v_isSharedCheck_3473_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3463_);
                        leanh::lean_inc(v_head_3462_);
                        leanh::lean_dec(v_x_3461_);
                        v___x_3465_ = leanh::lean_box(0);
                        v_isShared_3466_ = v_isSharedCheck_3473_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3459_);
                if v_isShared_3466_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3465_, 5);
                    leanh::lean_ctor_set(v___x_3465_, 1, v_x_3459_);
                    leanh::lean_ctor_set(v___x_3465_, 0, v_x_3460_);
                    v___x_3468_ = v___x_3465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_x_3460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_x_3459_);
                    v___x_3468_ = v_reuseFailAlloc_3472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3469_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3462_);
                v___x_3470_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3470_, 0, v___x_3468_);
                leanh::lean_ctor_set(v___x_3470_, 1, v___x_3469_);
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
    mut v_x_3474_: *mut leanh::LeanObject,
    mut v_x_3475_: *mut leanh::LeanObject,
    mut v_x_3476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3476_) == 0 {
                    leanh::lean_dec(v_x_3474_);
                    return v_x_3475_;
                } else {
                    v_head_3477_ = leanh::lean_ctor_get(v_x_3476_, 0);
                    v_tail_3478_ = leanh::lean_ctor_get(v_x_3476_, 1);
                    v_isSharedCheck_3488_ = (!leanh::lean_is_exclusive(v_x_3476_)) as u8;
                    if v_isSharedCheck_3488_ == 0 {
                        v___x_3480_ = v_x_3476_;
                        v_isShared_3481_ = v_isSharedCheck_3488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3478_);
                        leanh::lean_inc(v_head_3477_);
                        leanh::lean_dec(v_x_3476_);
                        v___x_3480_ = leanh::lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3474_);
                if v_isShared_3481_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3480_, 5);
                    leanh::lean_ctor_set(v___x_3480_, 1, v_x_3474_);
                    leanh::lean_ctor_set(v___x_3480_, 0, v_x_3475_);
                    v___x_3483_ = v___x_3480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_x_3475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_x_3474_);
                    v___x_3483_ = v_reuseFailAlloc_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3477_);
                v___x_3485_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3485_, 0, v___x_3483_);
                leanh::lean_ctor_set(v___x_3485_, 1, v___x_3484_);
                v___x_3486_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_3474_, v___x_3485_, v_tail_3478_);
                return v___x_3486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(
    mut v_x_3489_: *mut leanh::LeanObject,
    mut v_x_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3489_) == 0 {
        let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3490_);
        v___x_3491_ = leanh::lean_box(0);
        return v___x_3491_;
    } else {
        let mut v_tail_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_3492_ = leanh::lean_ctor_get(v_x_3489_, 1);
        if leanh::lean_obj_tag(v_tail_3492_) == 0 {
            let mut v_head_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_3490_);
            v_head_3493_ = leanh::lean_ctor_get(v_x_3489_, 0);
            leanh::lean_inc(v_head_3493_);
            leanh::lean_dec_ref_known(v_x_3489_, 2);
            v___x_3494_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3493_);
            return v___x_3494_;
        } else {
            let mut v_head_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_3492_);
            v_head_3495_ = leanh::lean_ctor_get(v_x_3489_, 0);
            leanh::lean_inc(v_head_3495_);
            leanh::lean_dec_ref_known(v_x_3489_, 2);
            v___x_3496_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_3495_);
            v___x_3497_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_3490_, v___x_3496_, v_tail_3492_);
            return v___x_3497_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0;
    v___x_3500_ = lean_string_length(v___x_3499_);
    return v___x_3500_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3501_ = leanh::lean_obj_once(
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
    mut v_xs_3508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    v___x_3509_ = lean_array_get_size(v_xs_3508_);
    v___x_3510_ = leanh::lean_unsigned_to_nat(0);
    v___x_3511_ = lean_nat_dec_eq(v___x_3509_, v___x_3510_);
    if v___x_3511_ == 0 {
        let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3512_ = lean_array_to_list(v_xs_3508_);
        v___x_3513_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_3514_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_3512_, v___x_3513_);
        v___x_3515_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
        v___x_3516_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3;
        v___x_3517_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3517_, 0, v___x_3516_);
        leanh::lean_ctor_set(v___x_3517_, 1, v___x_3514_);
        v___x_3518_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_3519_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3519_, 0, v___x_3517_);
        leanh::lean_ctor_set(v___x_3519_, 1, v___x_3518_);
        v___x_3520_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3520_, 0, v___x_3515_);
        leanh::lean_ctor_set(v___x_3520_, 1, v___x_3519_);
        v___x_3521_ = l_Std_Format_fill(v___x_3520_);
        return v___x_3521_;
    } else {
        let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_3508_);
        v___x_3522_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5;
        return v___x_3522_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(
    mut v_x_3523_: *mut leanh::LeanObject,
    mut v_x_3524_: *mut leanh::LeanObject,
    mut v_x_3525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3530_: u8 = 0;
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3525_) == 0 {
                    leanh::lean_dec(v_x_3523_);
                    return v_x_3524_;
                } else {
                    v_head_3526_ = leanh::lean_ctor_get(v_x_3525_, 0);
                    v_tail_3527_ = leanh::lean_ctor_get(v_x_3525_, 1);
                    v_isSharedCheck_3537_ = (!leanh::lean_is_exclusive(v_x_3525_)) as u8;
                    if v_isSharedCheck_3537_ == 0 {
                        v___x_3529_ = v_x_3525_;
                        v_isShared_3530_ = v_isSharedCheck_3537_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3527_);
                        leanh::lean_inc(v_head_3526_);
                        leanh::lean_dec(v_x_3525_);
                        v___x_3529_ = leanh::lean_box(0);
                        v_isShared_3530_ = v_isSharedCheck_3537_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3523_);
                if v_isShared_3530_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3529_, 5);
                    leanh::lean_ctor_set(v___x_3529_, 1, v_x_3523_);
                    leanh::lean_ctor_set(v___x_3529_, 0, v_x_3524_);
                    v___x_3532_ = v___x_3529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_x_3524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_x_3523_);
                    v___x_3532_ = v_reuseFailAlloc_3536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3533_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3526_);
                v___x_3534_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3534_, 0, v___x_3532_);
                leanh::lean_ctor_set(v___x_3534_, 1, v___x_3533_);
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
    mut v_x_3538_: *mut leanh::LeanObject,
    mut v_x_3539_: *mut leanh::LeanObject,
    mut v_x_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3540_) == 0 {
                    leanh::lean_dec(v_x_3538_);
                    return v_x_3539_;
                } else {
                    v_head_3541_ = leanh::lean_ctor_get(v_x_3540_, 0);
                    v_tail_3542_ = leanh::lean_ctor_get(v_x_3540_, 1);
                    v_isSharedCheck_3552_ = (!leanh::lean_is_exclusive(v_x_3540_)) as u8;
                    if v_isSharedCheck_3552_ == 0 {
                        v___x_3544_ = v_x_3540_;
                        v_isShared_3545_ = v_isSharedCheck_3552_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3542_);
                        leanh::lean_inc(v_head_3541_);
                        leanh::lean_dec(v_x_3540_);
                        v___x_3544_ = leanh::lean_box(0);
                        v_isShared_3545_ = v_isSharedCheck_3552_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_3538_);
                if v_isShared_3545_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3544_, 5);
                    leanh::lean_ctor_set(v___x_3544_, 1, v_x_3538_);
                    leanh::lean_ctor_set(v___x_3544_, 0, v_x_3539_);
                    v___x_3547_ = v___x_3544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3551_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_x_3539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_x_3538_);
                    v___x_3547_ = v_reuseFailAlloc_3551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3548_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3541_);
                v___x_3549_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3549_, 0, v___x_3547_);
                leanh::lean_ctor_set(v___x_3549_, 1, v___x_3548_);
                v___x_3550_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_3538_, v___x_3549_, v_tail_3542_);
                return v___x_3550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(
    mut v_x_3553_: *mut leanh::LeanObject,
    mut v_x_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3553_) == 0 {
        let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3554_);
        v___x_3555_ = leanh::lean_box(0);
        return v___x_3555_;
    } else {
        let mut v_tail_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_3556_ = leanh::lean_ctor_get(v_x_3553_, 1);
        if leanh::lean_obj_tag(v_tail_3556_) == 0 {
            let mut v_head_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_3554_);
            v_head_3557_ = leanh::lean_ctor_get(v_x_3553_, 0);
            leanh::lean_inc(v_head_3557_);
            leanh::lean_dec_ref_known(v_x_3553_, 2);
            v___x_3558_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3557_);
            return v___x_3558_;
        } else {
            let mut v_head_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_3556_);
            v_head_3559_ = leanh::lean_ctor_get(v_x_3553_, 0);
            leanh::lean_inc(v_head_3559_);
            leanh::lean_dec_ref_known(v_x_3553_, 2);
            v___x_3560_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_3559_);
            v___x_3561_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_3554_, v___x_3560_, v_tail_3556_);
            return v___x_3561_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(
    mut v_xs_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    v___x_3563_ = lean_array_get_size(v_xs_3562_);
    v___x_3564_ = leanh::lean_unsigned_to_nat(0);
    v___x_3565_ = lean_nat_dec_eq(v___x_3563_, v___x_3564_);
    if v___x_3565_ == 0 {
        let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3566_ = lean_array_to_list(v_xs_3562_);
        v___x_3567_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5;
        v___x_3568_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_3566_, v___x_3567_);
        v___x_3569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once), _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
        v___x_3570_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3;
        v___x_3571_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3571_, 0, v___x_3570_);
        leanh::lean_ctor_set(v___x_3571_, 1, v___x_3568_);
        v___x_3572_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10;
        v___x_3573_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
        leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
        v___x_3574_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3574_, 0, v___x_3569_);
        leanh::lean_ctor_set(v___x_3574_, 1, v___x_3573_);
        v___x_3575_ = l_Std_Format_fill(v___x_3574_);
        return v___x_3575_;
    } else {
        let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_3562_);
        v___x_3576_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5;
        return v___x_3576_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = leanh::lean_unsigned_to_nat(12);
    v___x_3593_ = lean_nat_to_int(v___x_3592_);
    return v___x_3593_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3600_ = leanh::lean_unsigned_to_nat(14);
    v___x_3601_ = lean_nat_to_int(v___x_3600_);
    return v___x_3601_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(
    mut v_x_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_altInfos_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uElimPos_x3f_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_overlaps_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_3606_ = leanh::lean_ctor_get(v_x_3605_, 0);
    leanh::lean_inc(v_numParams_3606_);
    v_numDiscrs_3607_ = leanh::lean_ctor_get(v_x_3605_, 1);
    leanh::lean_inc(v_numDiscrs_3607_);
    v_altInfos_3608_ = leanh::lean_ctor_get(v_x_3605_, 2);
    leanh::lean_inc_ref(v_altInfos_3608_);
    v_uElimPos_x3f_3609_ = leanh::lean_ctor_get(v_x_3605_, 3);
    leanh::lean_inc(v_uElimPos_x3f_3609_);
    v_discrInfos_3610_ = leanh::lean_ctor_get(v_x_3605_, 4);
    leanh::lean_inc_ref(v_discrInfos_3610_);
    v_overlaps_3611_ = leanh::lean_ctor_get(v_x_3605_, 5);
    leanh::lean_inc_ref(v_overlaps_3611_);
    leanh::lean_dec_ref(v_x_3605_);
    v___x_3612_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5;
    v___x_3613_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3;
    v___x_3614_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4,
    );
    v___x_3615_ = l_Nat_reprFast(v_numParams_3606_);
    v___x_3616_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3616_, 0, v___x_3615_);
    v___x_3617_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3617_, 0, v___x_3614_);
    leanh::lean_ctor_set(v___x_3617_, 1, v___x_3616_);
    v___x_3618_ = 0;
    v___x_3619_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3619_, 0, v___x_3617_);
    leanh::lean_ctor_set_uint8(
        v___x_3619_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3620_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3620_, 0, v___x_3613_);
    leanh::lean_ctor_set(v___x_3620_, 1, v___x_3619_);
    v___x_3621_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4;
    v___x_3622_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3622_, 0, v___x_3620_);
    leanh::lean_ctor_set(v___x_3622_, 1, v___x_3621_);
    v___x_3623_ = leanh::lean_box(1);
    v___x_3624_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3624_, 0, v___x_3622_);
    leanh::lean_ctor_set(v___x_3624_, 1, v___x_3623_);
    v___x_3625_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5;
    v___x_3626_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3626_, 0, v___x_3624_);
    leanh::lean_ctor_set(v___x_3626_, 1, v___x_3625_);
    v___x_3627_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3627_, 0, v___x_3626_);
    leanh::lean_ctor_set(v___x_3627_, 1, v___x_3612_);
    v___x_3628_ = l_Nat_reprFast(v_numDiscrs_3607_);
    v___x_3629_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
    v___x_3630_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3630_, 0, v___x_3614_);
    leanh::lean_ctor_set(v___x_3630_, 1, v___x_3629_);
    v___x_3631_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3631_, 0, v___x_3630_);
    leanh::lean_ctor_set_uint8(
        v___x_3631_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3632_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3632_, 0, v___x_3627_);
    leanh::lean_ctor_set(v___x_3632_, 1, v___x_3631_);
    v___x_3633_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3633_, 0, v___x_3632_);
    leanh::lean_ctor_set(v___x_3633_, 1, v___x_3621_);
    v___x_3634_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3634_, 0, v___x_3633_);
    leanh::lean_ctor_set(v___x_3634_, 1, v___x_3623_);
    v___x_3635_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7;
    v___x_3636_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3634_);
    leanh::lean_ctor_set(v___x_3636_, 1, v___x_3635_);
    v___x_3637_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3637_, 0, v___x_3636_);
    leanh::lean_ctor_set(v___x_3637_, 1, v___x_3612_);
    v___x_3638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once
        ),
        _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8,
    );
    v___x_3639_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_3608_);
    v___x_3640_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3640_, 0, v___x_3638_);
    leanh::lean_ctor_set(v___x_3640_, 1, v___x_3639_);
    v___x_3641_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3641_, 0, v___x_3640_);
    leanh::lean_ctor_set_uint8(
        v___x_3641_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3642_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3642_, 0, v___x_3637_);
    leanh::lean_ctor_set(v___x_3642_, 1, v___x_3641_);
    v___x_3643_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3643_, 0, v___x_3642_);
    leanh::lean_ctor_set(v___x_3643_, 1, v___x_3621_);
    v___x_3644_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
    leanh::lean_ctor_set(v___x_3644_, 1, v___x_3623_);
    v___x_3645_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10;
    v___x_3646_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3646_, 0, v___x_3644_);
    leanh::lean_ctor_set(v___x_3646_, 1, v___x_3645_);
    v___x_3647_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3647_, 0, v___x_3646_);
    leanh::lean_ctor_set(v___x_3647_, 1, v___x_3612_);
    v___x_3648_ = leanh::lean_unsigned_to_nat(0);
    v___x_3649_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(
        v_uElimPos_x3f_3609_,
        v___x_3648_,
    );
    v___x_3650_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3650_, 0, v___x_3614_);
    leanh::lean_ctor_set(v___x_3650_, 1, v___x_3649_);
    v___x_3651_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3651_, 0, v___x_3650_);
    leanh::lean_ctor_set_uint8(
        v___x_3651_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3652_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3652_, 0, v___x_3647_);
    leanh::lean_ctor_set(v___x_3652_, 1, v___x_3651_);
    v___x_3653_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3653_, 0, v___x_3652_);
    leanh::lean_ctor_set(v___x_3653_, 1, v___x_3621_);
    v___x_3654_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3654_, 0, v___x_3653_);
    leanh::lean_ctor_set(v___x_3654_, 1, v___x_3623_);
    v___x_3655_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12;
    v___x_3656_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3656_, 0, v___x_3654_);
    leanh::lean_ctor_set(v___x_3656_, 1, v___x_3655_);
    v___x_3657_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3657_, 0, v___x_3656_);
    leanh::lean_ctor_set(v___x_3657_, 1, v___x_3612_);
    v___x_3658_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13,
    );
    v___x_3659_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_3610_);
    v___x_3660_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3660_, 0, v___x_3658_);
    leanh::lean_ctor_set(v___x_3660_, 1, v___x_3659_);
    v___x_3661_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3661_, 0, v___x_3660_);
    leanh::lean_ctor_set_uint8(
        v___x_3661_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3662_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3662_, 0, v___x_3657_);
    leanh::lean_ctor_set(v___x_3662_, 1, v___x_3661_);
    v___x_3663_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3663_, 0, v___x_3662_);
    leanh::lean_ctor_set(v___x_3663_, 1, v___x_3621_);
    v___x_3664_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    leanh::lean_ctor_set(v___x_3664_, 1, v___x_3623_);
    v___x_3665_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15;
    v___x_3666_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3666_, 0, v___x_3664_);
    leanh::lean_ctor_set(v___x_3666_, 1, v___x_3665_);
    v___x_3667_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    leanh::lean_ctor_set(v___x_3667_, 1, v___x_3612_);
    v___x_3668_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_3611_);
    v___x_3669_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3669_, 0, v___x_3638_);
    leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
    v___x_3670_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3670_, 0, v___x_3669_);
    leanh::lean_ctor_set_uint8(
        v___x_3670_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    v___x_3671_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3671_, 0, v___x_3667_);
    leanh::lean_ctor_set(v___x_3671_, 1, v___x_3670_);
    v___x_3672_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10,
    );
    v___x_3673_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11;
    v___x_3674_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3674_, 0, v___x_3673_);
    leanh::lean_ctor_set(v___x_3674_, 1, v___x_3671_);
    v___x_3675_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12;
    v___x_3676_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3676_, 0, v___x_3674_);
    leanh::lean_ctor_set(v___x_3676_, 1, v___x_3675_);
    v___x_3677_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3677_, 0, v___x_3672_);
    leanh::lean_ctor_set(v___x_3677_, 1, v___x_3676_);
    v___x_3678_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    leanh::lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3618_,
    );
    return v___x_3678_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr(
    mut v_x_3679_: *mut leanh::LeanObject,
    mut v_prec_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3681_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_3679_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(
    mut v_x_3682_: *mut leanh::LeanObject,
    mut v_prec_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_3682_, v_prec_3683_);
    leanh::lean_dec(v_prec_3683_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_numAlts(
    mut v_info_3687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_altInfos_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_altInfos_3688_ = leanh::lean_ctor_get(v_info_3687_, 2);
    v___x_3689_ = lean_array_get_size(v_altInfos_3688_);
    return v___x_3689_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(
    mut v_info_3690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3691_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3690_);
    leanh::lean_dec_ref(v_info_3690_);
    return v_res_3691_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_arity(
    mut v_info_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_3693_ = leanh::lean_ctor_get(v_info_3692_, 0);
    v_numDiscrs_3694_ = leanh::lean_ctor_get(v_info_3692_, 1);
    v___x_3695_ = leanh::lean_unsigned_to_nat(1);
    v___x_3696_ = lean_nat_add(v_numParams_3693_, v___x_3695_);
    v___x_3697_ = lean_nat_add(v___x_3696_, v_numDiscrs_3694_);
    leanh::lean_dec(v___x_3696_);
    v___x_3698_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3692_);
    v___x_3699_ = lean_nat_add(v___x_3697_, v___x_3698_);
    leanh::lean_dec(v___x_3698_);
    leanh::lean_dec(v___x_3697_);
    return v___x_3699_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_arity___boxed(
    mut v_info_3700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_3700_);
    leanh::lean_dec_ref(v_info_3700_);
    return v_res_3701_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(
    mut v_info_3702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_3703_ = leanh::lean_ctor_get(v_info_3702_, 0);
    v___x_3704_ = leanh::lean_unsigned_to_nat(1);
    v___x_3705_ = lean_nat_add(v_numParams_3703_, v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(
    mut v_info_3706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_3706_);
    leanh::lean_dec_ref(v_info_3706_);
    return v_res_3707_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getDiscrRange(
    mut v_info_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numDiscrs_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numDiscrs_3709_ = leanh::lean_ctor_get(v_info_3708_, 1);
    v___x_3710_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_3708_);
    v___x_3711_ = lean_nat_add(v___x_3710_, v_numDiscrs_3709_);
    v___x_3712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3712_, 0, v___x_3710_);
    leanh::lean_ctor_set(v___x_3712_, 1, v___x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(
    mut v_info_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3714_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_3713_);
    leanh::lean_dec_ref(v_info_3713_);
    return v_res_3714_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(
    mut v_info_3715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_3716_ = leanh::lean_ctor_get(v_info_3715_, 0);
    v_numDiscrs_3717_ = leanh::lean_ctor_get(v_info_3715_, 1);
    v___x_3718_ = leanh::lean_unsigned_to_nat(1);
    v___x_3719_ = lean_nat_add(v_numParams_3716_, v___x_3718_);
    v___x_3720_ = lean_nat_add(v___x_3719_, v_numDiscrs_3717_);
    leanh::lean_dec(v___x_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(
    mut v_info_3721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3722_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_3721_);
    leanh::lean_dec_ref(v_info_3721_);
    return v_res_3722_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getAltRange(
    mut v_info_3723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_3723_);
    v___x_3725_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_3723_);
    v___x_3726_ = lean_nat_add(v___x_3724_, v___x_3725_);
    leanh::lean_dec(v___x_3725_);
    v___x_3727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3727_, 0, v___x_3724_);
    leanh::lean_ctor_set(v___x_3727_, 1, v___x_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(
    mut v_info_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_3728_);
    leanh::lean_dec_ref(v_info_3728_);
    return v_res_3729_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getMotivePos(
    mut v_info_3730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_3731_ = leanh::lean_ctor_get(v_info_3730_, 0);
    leanh::lean_inc(v_numParams_3731_);
    return v_numParams_3731_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(
    mut v_info_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3733_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_3732_);
    leanh::lean_dec_ref(v_info_3732_);
    return v_res_3733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(
    mut v_as_3734_: *mut leanh::LeanObject,
    mut v_sz_3735_: usize,
    mut v_i_3736_: usize,
    mut v_b_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: usize = 0;
    let mut v___x_3741_: usize = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v_a_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3743_ = lean_usize_dec_lt(v_i_3736_, v_sz_3735_);
                if v___x_3743_ == 0 {
                    return v_b_3737_;
                } else {
                    v_a_3744_ = lean_array_uget_borrowed(v_as_3734_, v_i_3736_);
                    if leanh::lean_obj_tag(v_a_3744_) == 0 {
                        v_a_3739_ = v_b_3737_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3745_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3746_ = lean_nat_add(v_b_3737_, v___x_3745_);
                        leanh::lean_dec(v_b_3737_);
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
    mut v_as_3747_: *mut leanh::LeanObject,
    mut v_sz_3748_: *mut leanh::LeanObject,
    mut v_i_3749_: *mut leanh::LeanObject,
    mut v_b_3750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3751_: usize = 0;
    let mut v_i_boxed_3752_: usize = 0;
    let mut v_res_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3751_ = leanh::lean_unbox_usize(v_sz_3748_);
    leanh::lean_dec(v_sz_3748_);
    v_i_boxed_3752_ = leanh::lean_unbox_usize(v_i_3749_);
    leanh::lean_dec(v_i_3749_);
    v_res_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_3747_, v_sz_boxed_3751_, v_i_boxed_3752_, v_b_3750_);
    leanh::lean_dec_ref(v_as_3747_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Meta_Match_getNumEqsFromDiscrInfos(
    mut v_infos_3754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3756_: usize = 0;
    let mut v___x_3757_: usize = 0;
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_3755_ = leanh::lean_unsigned_to_nat(0);
    v_sz_3756_ = lean_array_size(v_infos_3754_);
    v___x_3757_ = 0usize;
    v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_3754_, v_sz_3756_, v___x_3757_, v_r_3755_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(
    mut v_infos_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_3759_);
    leanh::lean_dec_ref(v_infos_3759_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(
    mut v_info_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_discrInfos_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_discrInfos_3762_ = leanh::lean_ctor_get(v_info_3761_, 4);
    v___x_3763_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3762_);
    return v___x_3763_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(
    mut v_info_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_3764_);
    leanh::lean_dec_ref(v_info_3764_);
    return v_res_3765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(
    mut v_info_3766_: *mut leanh::LeanObject,
    mut v_sz_3767_: usize,
    mut v_i_3768_: usize,
    mut v_bs_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3770_: u8 = 0;
    let mut v_v_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numOverlaps_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_3774_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: usize = 0;
    let mut v___x_3784_: usize = 0;
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = lean_usize_dec_lt(v_i_3768_, v_sz_3767_);
                if v___x_3770_ == 0 {
                    return v_bs_3769_;
                } else {
                    v_v_3771_ = lean_array_uget_borrowed(v_bs_3769_, v_i_3768_);
                    v_numFields_3772_ = leanh::lean_ctor_get(v_v_3771_, 0);
                    leanh::lean_inc(v_numFields_3772_);
                    v_numOverlaps_3773_ = leanh::lean_ctor_get(v_v_3771_, 1);
                    leanh::lean_inc(v_numOverlaps_3773_);
                    v_hasUnitThunk_3774_ = leanh::lean_ctor_get_uint8(
                        v_v_3771_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_3775_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3776_ = lean_array_uset(v_bs_3769_, v_i_3768_, v___x_3775_);
                    v___x_3777_ = lean_nat_add(v_numFields_3772_, v_numOverlaps_3773_);
                    leanh::lean_dec(v_numOverlaps_3773_);
                    leanh::lean_dec(v_numFields_3772_);
                    if v_hasUnitThunk_3774_ == 0 {
                        v___y_3779_ = v___x_3775_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3787_ = leanh::lean_unsigned_to_nat(1);
                        v___y_3779_ = v___x_3787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3780_ = lean_nat_add(v___x_3777_, v___y_3779_);
                leanh::lean_dec(v___y_3779_);
                leanh::lean_dec(v___x_3777_);
                v___x_3781_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_3766_);
                v___x_3782_ = lean_nat_add(v___x_3780_, v___x_3781_);
                leanh::lean_dec(v___x_3781_);
                leanh::lean_dec(v___x_3780_);
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
    mut v_info_3788_: *mut leanh::LeanObject,
    mut v_sz_3789_: *mut leanh::LeanObject,
    mut v_i_3790_: *mut leanh::LeanObject,
    mut v_bs_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3792_: usize = 0;
    let mut v_i_boxed_3793_: usize = 0;
    let mut v_res_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3792_ = leanh::lean_unbox_usize(v_sz_3789_);
    leanh::lean_dec(v_sz_3789_);
    v_i_boxed_3793_ = leanh::lean_unbox_usize(v_i_3790_);
    leanh::lean_dec(v_i_3790_);
    v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_3788_, v_sz_boxed_3792_, v_i_boxed_3793_, v_bs_3791_);
    leanh::lean_dec_ref(v_info_3788_);
    return v_res_3794_;
}
pub unsafe fn l_Lean_Meta_Match_MatcherInfo_altNumParams(
    mut v_info_3795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_altInfos_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3797_: usize = 0;
    let mut v___x_3798_: usize = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_altInfos_3796_ = leanh::lean_ctor_get(v_info_3795_, 2);
    leanh::lean_inc_ref(v_altInfos_3796_);
    v_sz_3797_ = lean_array_size(v_altInfos_3796_);
    v___x_3798_ = 0usize;
    v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_3795_, v_sz_3797_, v___x_3798_, v_altInfos_3796_);
    leanh::lean_dec_ref(v_info_3795_);
    return v___x_3799_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = leanh::lean_box(0);
    v___x_3801_ = leanh::lean_unsigned_to_nat(16);
    v___x_3802_ = lean_mk_array(v___x_3801_, v___x_3800_);
    return v___x_3802_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0,
    );
    v___x_3804_ = leanh::lean_unsigned_to_nat(0);
    v___x_3805_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3804_);
    leanh::lean_ctor_set(v___x_3805_, 1, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3806_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3806_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2,
    );
    v___x_3808_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3808_, 0, v___x_3807_);
    return v___x_3808_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3,
    );
    v___x_3810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1,
    );
    v___x_3811_ = 1;
    v___x_3812_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_3812_, 0, v___x_3810_);
    leanh::lean_ctor_set(v___x_3812_, 1, v___x_3809_);
    leanh::lean_ctor_set_uint8(
        v___x_3812_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_3811_,
    );
    return v___x_3812_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_instInhabitedState() -> *mut leanh::LeanObject
{
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3813_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once),
        _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4,
    );
    return v___x_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_x_3815_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3816_: u8 = 0;
    let mut v_key_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3815_) == 0 {
                    v___x_3816_ = 0;
                    return v___x_3816_;
                } else {
                    v_key_3817_ = leanh::lean_ctor_get(v_x_3815_, 0);
                    v_tail_3818_ = leanh::lean_ctor_get(v_x_3815_, 2);
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
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_x_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3823_: u8 = 0;
    let mut v_r_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_3821_, v_x_3822_);
    leanh::lean_dec(v_x_3822_);
    leanh::lean_dec(v_a_3821_);
    v_r_3824_ = leanh::lean_box((v_res_3823_) as usize);
    return v_r_3824_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0()
-> u64 {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u64 = 0;
    v___x_3825_ = leanh::lean_unsigned_to_nat(1723);
    v___x_3826_ = lean_uint64_of_nat(v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_3827_: *mut leanh::LeanObject,
    mut v_x_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3834_: u8 = 0;
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u64 = 0;
    let mut v_hash_3856_: u64 = 0;
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3828_) == 0 {
                    return v_x_3827_;
                } else {
                    v_key_3829_ = leanh::lean_ctor_get(v_x_3828_, 0);
                    v_value_3830_ = leanh::lean_ctor_get(v_x_3828_, 1);
                    v_tail_3831_ = leanh::lean_ctor_get(v_x_3828_, 2);
                    v_isSharedCheck_3857_ = (!leanh::lean_is_exclusive(v_x_3828_)) as u8;
                    if v_isSharedCheck_3857_ == 0 {
                        v___x_3833_ = v_x_3828_;
                        v_isShared_3834_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3831_);
                        leanh::lean_inc(v_value_3830_);
                        leanh::lean_inc(v_key_3829_);
                        leanh::lean_dec(v_x_3828_);
                        v___x_3833_ = leanh::lean_box(0);
                        v_isShared_3834_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3835_ = lean_array_get_size(v_x_3827_);
                if leanh::lean_obj_tag(v_key_3829_) == 0 {
                    v___x_3855_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_3837_ = v___x_3855_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3856_ = leanh::lean_ctor_get_uint64(
                        v_key_3829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_3849_);
                if v_isShared_3834_ == 0 {
                    leanh::lean_ctor_set(v___x_3833_, 2, v___x_3849_);
                    v___x_3851_ = v___x_3833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_key_3829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_value_3830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 2, v___x_3849_);
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
    mut v_i_3858_: *mut leanh::LeanObject,
    mut v_source_3859_: *mut leanh::LeanObject,
    mut v_target_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v_es_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = lean_array_get_size(v_source_3859_);
                v___x_3862_ = lean_nat_dec_lt(v_i_3858_, v___x_3861_);
                if v___x_3862_ == 0 {
                    leanh::lean_dec_ref(v_source_3859_);
                    leanh::lean_dec(v_i_3858_);
                    return v_target_3860_;
                } else {
                    v_es_3863_ = lean_array_fget(v_source_3859_, v_i_3858_);
                    v___x_3864_ = leanh::lean_box(0);
                    v_source_3865_ = lean_array_fset(v_source_3859_, v_i_3858_, v___x_3864_);
                    v_target_3866_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_3860_, v_es_3863_);
                    v___x_3867_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3868_ = lean_nat_add(v_i_3858_, v___x_3867_);
                    leanh::lean_dec(v_i_3858_);
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
    mut v_data_3870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = lean_array_get_size(v_data_3870_);
    v___x_3872_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3873_ = lean_nat_mul(v___x_3871_, v___x_3872_);
    v___x_3874_ = leanh::lean_unsigned_to_nat(0);
    v___x_3875_ = leanh::lean_box(0);
    v___x_3876_ = lean_mk_array(v_nbuckets_3873_, v___x_3875_);
    v___x_3877_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_3874_, v_data_3870_, v___x_3876_);
    return v___x_3877_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_b_3879_: *mut leanh::LeanObject,
    mut v_x_3880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3880_) == 0 {
                    leanh::lean_dec(v_b_3879_);
                    leanh::lean_dec(v_a_3878_);
                    return v_x_3880_;
                } else {
                    v_key_3881_ = leanh::lean_ctor_get(v_x_3880_, 0);
                    v_value_3882_ = leanh::lean_ctor_get(v_x_3880_, 1);
                    v_tail_3883_ = leanh::lean_ctor_get(v_x_3880_, 2);
                    v_isSharedCheck_3895_ = (!leanh::lean_is_exclusive(v_x_3880_)) as u8;
                    if v_isSharedCheck_3895_ == 0 {
                        v___x_3885_ = v_x_3880_;
                        v_isShared_3886_ = v_isSharedCheck_3895_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3883_);
                        leanh::lean_inc(v_value_3882_);
                        leanh::lean_inc(v_key_3881_);
                        leanh::lean_dec(v_x_3880_);
                        v___x_3885_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_3885_, 2, v___x_3888_);
                        v___x_3890_ = v___x_3885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_key_3881_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_value_3882_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 2, v___x_3888_);
                        v___x_3890_ = v_reuseFailAlloc_3891_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3882_);
                    leanh::lean_dec(v_key_3881_);
                    if v_isShared_3886_ == 0 {
                        leanh::lean_ctor_set(v___x_3885_, 1, v_b_3879_);
                        leanh::lean_ctor_set(v___x_3885_, 0, v_a_3878_);
                        v___x_3893_ = v___x_3885_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3894_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3878_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_b_3879_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_tail_3883_);
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
    mut v_m_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_b_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: u8 = 0;
    let mut v_val_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u64 = 0;
    let mut v_hash_3945_: u64 = 0;
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3899_ = leanh::lean_ctor_get(v_m_3896_, 0);
                v_buckets_3900_ = leanh::lean_ctor_get(v_m_3896_, 1);
                v_isSharedCheck_3946_ = (!leanh::lean_is_exclusive(v_m_3896_)) as u8;
                if v_isSharedCheck_3946_ == 0 {
                    v___x_3902_ = v_m_3896_;
                    v_isShared_3903_ = v_isSharedCheck_3946_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3900_);
                    leanh::lean_inc(v_size_3899_);
                    leanh::lean_dec(v_m_3896_);
                    v___x_3902_ = leanh::lean_box(0);
                    v_isShared_3903_ = v_isSharedCheck_3946_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3904_ = lean_array_get_size(v_buckets_3900_);
                if leanh::lean_obj_tag(v_a_3897_) == 0 {
                    v___x_3944_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_3906_ = v___x_3944_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3945_ = leanh::lean_ctor_get_uint64(
                        v_a_3897_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    v___x_3920_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3921_ = lean_nat_add(v_size_3899_, v___x_3920_);
                    leanh::lean_dec(v_size_3899_);
                    leanh::lean_inc(v_bkt_3918_);
                    v___x_3922_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3922_, 0, v_a_3897_);
                    leanh::lean_ctor_set(v___x_3922_, 1, v_b_3898_);
                    leanh::lean_ctor_set(v___x_3922_, 2, v_bkt_3918_);
                    v_buckets_x27_3923_ =
                        lean_array_uset(v_buckets_3900_, v___x_3917_, v___x_3922_);
                    v___x_3924_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3925_ = lean_nat_mul(v_size_x27_3921_, v___x_3924_);
                    v___x_3926_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3927_ = lean_nat_div(v___x_3925_, v___x_3926_);
                    leanh::lean_dec(v___x_3925_);
                    v___x_3928_ = lean_array_get_size(v_buckets_x27_3923_);
                    v___x_3929_ = lean_nat_dec_le(v___x_3927_, v___x_3928_);
                    leanh::lean_dec(v___x_3927_);
                    if v___x_3929_ == 0 {
                        v_val_3930_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_3923_);
                        if v_isShared_3903_ == 0 {
                            leanh::lean_ctor_set(v___x_3902_, 1, v_val_3930_);
                            leanh::lean_ctor_set(v___x_3902_, 0, v_size_x27_3921_);
                            v___x_3932_ = v___x_3902_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3933_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3933_,
                                0,
                                v_size_x27_3921_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_val_3930_);
                            v___x_3932_ = v_reuseFailAlloc_3933_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3903_ == 0 {
                            leanh::lean_ctor_set(v___x_3902_, 1, v_buckets_x27_3923_);
                            leanh::lean_ctor_set(v___x_3902_, 0, v_size_x27_3921_);
                            v___x_3935_ = v___x_3902_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3936_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3936_,
                                0,
                                v_size_x27_3921_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3936_,
                                1,
                                v_buckets_x27_3923_,
                            );
                            v___x_3935_ = v_reuseFailAlloc_3936_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3918_);
                    v___x_3937_ = leanh::lean_box(0);
                    v_buckets_x27_3938_ =
                        lean_array_uset(v_buckets_3900_, v___x_3917_, v___x_3937_);
                    v___x_3939_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_3897_, v_b_3898_, v_bkt_3918_);
                    v___x_3940_ = lean_array_uset(v_buckets_x27_3938_, v___x_3917_, v___x_3939_);
                    if v_isShared_3903_ == 0 {
                        leanh::lean_ctor_set(v___x_3902_, 1, v___x_3940_);
                        v___x_3942_ = v___x_3902_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_size_3899_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3940_);
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
    mut v_x_3947_: *mut leanh::LeanObject,
    mut v_x_3948_: *mut leanh::LeanObject,
    mut v_x_3949_: *mut leanh::LeanObject,
    mut v_x_3950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3951_ = leanh::lean_ctor_get(v_x_3947_, 0);
                v_vs_3952_ = leanh::lean_ctor_get(v_x_3947_, 1);
                v_isSharedCheck_3976_ = (!leanh::lean_is_exclusive(v_x_3947_)) as u8;
                if v_isSharedCheck_3976_ == 0 {
                    v___x_3954_ = v_x_3947_;
                    v_isShared_3955_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3952_);
                    leanh::lean_inc(v_ks_3951_);
                    leanh::lean_dec(v_x_3947_);
                    v___x_3954_ = leanh::lean_box(0);
                    v_isShared_3955_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3956_ = lean_array_get_size(v_ks_3951_);
                v___x_3957_ = lean_nat_dec_lt(v_x_3948_, v___x_3956_);
                if v___x_3957_ == 0 {
                    leanh::lean_dec(v_x_3948_);
                    v___x_3958_ = lean_array_push(v_ks_3951_, v_x_3949_);
                    v___x_3959_ = lean_array_push(v_vs_3952_, v_x_3950_);
                    if v_isShared_3955_ == 0 {
                        leanh::lean_ctor_set(v___x_3954_, 1, v___x_3959_);
                        leanh::lean_ctor_set(v___x_3954_, 0, v___x_3958_);
                        v___x_3961_ = v___x_3954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3962_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3958_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3959_);
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
                            v_reuseFailAlloc_3970_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_ks_3951_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_vs_3952_);
                            v___x_3966_ = v_reuseFailAlloc_3970_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3971_ = lean_array_fset(v_ks_3951_, v_x_3948_, v_x_3949_);
                        v___x_3972_ = lean_array_fset(v_vs_3952_, v_x_3948_, v_x_3950_);
                        leanh::lean_dec(v_x_3948_);
                        if v_isShared_3955_ == 0 {
                            leanh::lean_ctor_set(v___x_3954_, 1, v___x_3972_);
                            leanh::lean_ctor_set(v___x_3954_, 0, v___x_3971_);
                            v___x_3974_ = v___x_3954_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3975_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3971_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3972_);
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
                v___x_3967_ = leanh::lean_unsigned_to_nat(1);
                v___x_3968_ = lean_nat_add(v_x_3948_, v___x_3967_);
                leanh::lean_dec(v_x_3948_);
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
    mut v_n_3977_: *mut leanh::LeanObject,
    mut v_k_3978_: *mut leanh::LeanObject,
    mut v_v_3979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_3986_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_3987_ = lean_usize_sub(v___x_3986_, v___x_3985_);
    return v___x_3987_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3988_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_3989_: *mut leanh::LeanObject,
    mut v_x_3990_: usize,
    mut v_x_3991_: usize,
    mut v_x_3992_: *mut leanh::LeanObject,
    mut v_x_3993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: usize = 0;
    let mut v___x_3997_: usize = 0;
    let mut v___x_3998_: usize = 0;
    let mut v_j_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_v_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v_node_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4029_: u8 = 0;
    let mut v___x_4030_: usize = 0;
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4049_: u8 = 0;
    let mut v_ks_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: usize = 0;
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: u8 = 0;
    let mut v_reuseFailAlloc_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3989_) == 0 {
                    v_es_3994_ = leanh::lean_ctor_get(v_x_3989_, 0);
                    v___x_3995_ = 5usize;
                    v___x_3996_ = 1usize;
                    v___x_3997_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3998_ = lean_usize_land(v_x_3990_, v___x_3997_);
                    v_j_3999_ = lean_usize_to_nat(v___x_3998_);
                    v___x_4000_ = lean_array_get_size(v_es_3994_);
                    v___x_4001_ = lean_nat_dec_lt(v_j_3999_, v___x_4000_);
                    if v___x_4001_ == 0 {
                        leanh::lean_dec(v_j_3999_);
                        leanh::lean_dec(v_x_3993_);
                        leanh::lean_dec(v_x_3992_);
                        return v_x_3989_;
                    } else {
                        leanh::lean_inc_ref(v_es_3994_);
                        v_isSharedCheck_4038_ = (!leanh::lean_is_exclusive(v_x_3989_)) as u8;
                        if v_isSharedCheck_4038_ == 0 {
                            v_unused_4039_ = leanh::lean_ctor_get(v_x_3989_, 0);
                            leanh::lean_dec(v_unused_4039_);
                            v___x_4003_ = v_x_3989_;
                            v_isShared_4004_ = v_isSharedCheck_4038_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3989_);
                            v___x_4003_ = leanh::lean_box(0);
                            v_isShared_4004_ = v_isSharedCheck_4038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4040_ = leanh::lean_ctor_get(v_x_3989_, 0);
                    v_vs_4041_ = leanh::lean_ctor_get(v_x_3989_, 1);
                    v_isSharedCheck_4061_ = (!leanh::lean_is_exclusive(v_x_3989_)) as u8;
                    if v_isSharedCheck_4061_ == 0 {
                        v___x_4043_ = v_x_3989_;
                        v_isShared_4044_ = v_isSharedCheck_4061_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4041_);
                        leanh::lean_inc(v_ks_4040_);
                        leanh::lean_dec(v_x_3989_);
                        v___x_4043_ = leanh::lean_box(0);
                        v_isShared_4044_ = v_isSharedCheck_4061_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4005_ = lean_array_fget(v_es_3994_, v_j_3999_);
                v___x_4006_ = leanh::lean_box(0);
                v_xs_x27_4007_ = lean_array_fset(v_es_3994_, v_j_3999_, v___x_4006_);
                match leanh::lean_obj_tag(v_v_4005_) {
                    0 => {
                        v_key_4014_ = leanh::lean_ctor_get(v_v_4005_, 0);
                        v_val_4015_ = leanh::lean_ctor_get(v_v_4005_, 1);
                        v_isSharedCheck_4025_ = (!leanh::lean_is_exclusive(v_v_4005_)) as u8;
                        if v_isSharedCheck_4025_ == 0 {
                            v___x_4017_ = v_v_4005_;
                            v_isShared_4018_ = v_isSharedCheck_4025_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4015_);
                            leanh::lean_inc(v_key_4014_);
                            leanh::lean_dec(v_v_4005_);
                            v___x_4017_ = leanh::lean_box(0);
                            v_isShared_4018_ = v_isSharedCheck_4025_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4026_ = leanh::lean_ctor_get(v_v_4005_, 0);
                        v_isSharedCheck_4036_ = (!leanh::lean_is_exclusive(v_v_4005_)) as u8;
                        if v_isSharedCheck_4036_ == 0 {
                            v___x_4028_ = v_v_4005_;
                            v_isShared_4029_ = v_isSharedCheck_4036_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4026_);
                            leanh::lean_dec(v_v_4005_);
                            v___x_4028_ = leanh::lean_box(0);
                            v_isShared_4029_ = v_isSharedCheck_4036_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4037_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4037_, 0, v_x_3992_);
                        leanh::lean_ctor_set(v___x_4037_, 1, v_x_3993_);
                        v___y_4009_ = v___x_4037_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4010_ = lean_array_fset(v_xs_x27_4007_, v_j_3999_, v___y_4009_);
                leanh::lean_dec(v_j_3999_);
                if v_isShared_4004_ == 0 {
                    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4010_);
                    v___x_4012_ = v___x_4003_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
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
                    leanh::lean_del_object(v___x_4017_);
                    v___x_4020_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4014_,
                        v_val_4015_,
                        v_x_3992_,
                        v_x_3993_,
                    );
                    v___x_4021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4021_, 0, v___x_4020_);
                    v___y_4009_ = v___x_4021_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4015_);
                    leanh::lean_dec(v_key_4014_);
                    if v_isShared_4018_ == 0 {
                        leanh::lean_ctor_set(v___x_4017_, 1, v_x_3993_);
                        leanh::lean_ctor_set(v___x_4017_, 0, v_x_3992_);
                        v___x_4023_ = v___x_4017_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4024_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_x_3992_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_x_3993_);
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
                    leanh::lean_ctor_set(v___x_4028_, 0, v___x_4032_);
                    v___x_4034_ = v___x_4028_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
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
                    v_reuseFailAlloc_4060_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_ks_4040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_vs_4041_);
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
                    v___x_4058_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4059_ = lean_nat_dec_lt(v___x_4057_, v___x_4058_);
                    leanh::lean_dec(v___x_4057_);
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
                    v_ks_4050_ = leanh::lean_ctor_get(v_newNode_4047_, 0);
                    leanh::lean_inc_ref(v_ks_4050_);
                    v_vs_4051_ = leanh::lean_ctor_get(v_newNode_4047_, 1);
                    leanh::lean_inc_ref(v_vs_4051_);
                    leanh::lean_dec_ref(v_newNode_4047_);
                    v___x_4052_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4053_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_4054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3991_, v_ks_4050_, v_vs_4051_, v___x_4052_, v___x_4053_);
                    leanh::lean_dec_ref(v_vs_4051_);
                    leanh::lean_dec_ref(v_ks_4050_);
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
    mut v_keys_4063_: *mut leanh::LeanObject,
    mut v_vals_4064_: *mut leanh::LeanObject,
    mut v_i_4065_: *mut leanh::LeanObject,
    mut v_entries_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u8 = 0;
    let mut v_k_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: u64 = 0;
    let mut v_h_4073_: usize = 0;
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: usize = 0;
    let mut v___x_4077_: usize = 0;
    let mut v___x_4078_: usize = 0;
    let mut v_h_4079_: usize = 0;
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u64 = 0;
    let mut v_hash_4084_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4067_ = lean_array_get_size(v_keys_4063_);
                v___x_4068_ = lean_nat_dec_lt(v_i_4065_, v___x_4067_);
                if v___x_4068_ == 0 {
                    leanh::lean_dec(v_i_4065_);
                    return v_entries_4066_;
                } else {
                    v_k_4069_ = lean_array_fget_borrowed(v_keys_4063_, v_i_4065_);
                    v_v_4070_ = lean_array_fget_borrowed(v_vals_4064_, v_i_4065_);
                    if leanh::lean_obj_tag(v_k_4069_) == 0 {
                        v___x_4083_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                        v___y_4072_ = v___x_4083_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4084_ = leanh::lean_ctor_get_uint64(
                            v_k_4069_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                v___x_4075_ = leanh::lean_unsigned_to_nat(1);
                v___x_4076_ = 1usize;
                v___x_4077_ = lean_usize_sub(v_depth_4062_, v___x_4076_);
                v___x_4078_ = lean_usize_mul(v___x_4074_, v___x_4077_);
                v_h_4079_ = lean_usize_shift_right(v_h_4073_, v___x_4078_);
                v___x_4080_ = lean_nat_add(v_i_4065_, v___x_4075_);
                leanh::lean_dec(v_i_4065_);
                leanh::lean_inc(v_v_4070_);
                leanh::lean_inc(v_k_4069_);
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
    mut v_depth_4085_: *mut leanh::LeanObject,
    mut v_keys_4086_: *mut leanh::LeanObject,
    mut v_vals_4087_: *mut leanh::LeanObject,
    mut v_i_4088_: *mut leanh::LeanObject,
    mut v_entries_4089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4090_: usize = 0;
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4090_ = leanh::lean_unbox_usize(v_depth_4085_);
    leanh::lean_dec(v_depth_4085_);
    v_res_4091_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_4090_, v_keys_4086_, v_vals_4087_, v_i_4088_, v_entries_4089_);
    leanh::lean_dec_ref(v_vals_4087_);
    leanh::lean_dec_ref(v_keys_4086_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4092_: *mut leanh::LeanObject,
    mut v_x_4093_: *mut leanh::LeanObject,
    mut v_x_4094_: *mut leanh::LeanObject,
    mut v_x_4095_: *mut leanh::LeanObject,
    mut v_x_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1022__boxed_4097_: usize = 0;
    let mut v_x_1023__boxed_4098_: usize = 0;
    let mut v_res_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1022__boxed_4097_ = leanh::lean_unbox_usize(v_x_4093_);
    leanh::lean_dec(v_x_4093_);
    v_x_1023__boxed_4098_ = leanh::lean_unbox_usize(v_x_4094_);
    leanh::lean_dec(v_x_4094_);
    v_res_4099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_4092_, v_x_1022__boxed_4097_, v_x_1023__boxed_4098_, v_x_4095_, v_x_4096_);
    return v_res_4099_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(
    mut v_x_4100_: *mut leanh::LeanObject,
    mut v_x_4101_: *mut leanh::LeanObject,
    mut v_x_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4104_: u64 = 0;
    let mut v___x_4105_: usize = 0;
    let mut v___x_4106_: usize = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u64 = 0;
    let mut v_hash_4109_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4101_) == 0 {
                    v___x_4108_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4104_ = v___x_4108_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4109_ = leanh::lean_ctor_get_uint64(
                        v_x_4101_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_4110_: *mut leanh::LeanObject,
    mut v_x_4111_: *mut leanh::LeanObject,
    mut v_x_4112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4113_: u8 = 0;
    let mut v_map_u2081_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_map_u2081_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4113_ = leanh::lean_ctor_get_uint8(
                    v_x_4110_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4113_ == 0 {
                    v_map_u2081_4114_ = leanh::lean_ctor_get(v_x_4110_, 0);
                    v_map_u2082_4115_ = leanh::lean_ctor_get(v_x_4110_, 1);
                    v_isSharedCheck_4123_ = (!leanh::lean_is_exclusive(v_x_4110_)) as u8;
                    if v_isSharedCheck_4123_ == 0 {
                        v___x_4117_ = v_x_4110_;
                        v_isShared_4118_ = v_isSharedCheck_4123_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4115_);
                        leanh::lean_inc(v_map_u2081_4114_);
                        leanh::lean_dec(v_x_4110_);
                        v___x_4117_ = leanh::lean_box(0);
                        v_isShared_4118_ = v_isSharedCheck_4123_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_4124_ = leanh::lean_ctor_get(v_x_4110_, 0);
                    v_map_u2082_4125_ = leanh::lean_ctor_get(v_x_4110_, 1);
                    v_isSharedCheck_4133_ = (!leanh::lean_is_exclusive(v_x_4110_)) as u8;
                    if v_isSharedCheck_4133_ == 0 {
                        v___x_4127_ = v_x_4110_;
                        v_isShared_4128_ = v_isSharedCheck_4133_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4125_);
                        leanh::lean_inc(v_map_u2081_4124_);
                        leanh::lean_dec(v_x_4110_);
                        v___x_4127_ = leanh::lean_box(0);
                        v_isShared_4128_ = v_isSharedCheck_4133_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4119_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2082_4115_, v_x_4111_, v_x_4112_);
                if v_isShared_4118_ == 0 {
                    leanh::lean_ctor_set(v___x_4117_, 1, v___x_4119_);
                    v___x_4121_ = v___x_4117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_map_u2081_4114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 1, v___x_4119_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4122_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_ctor_set(v___x_4127_, 0, v___x_4129_);
                    v___x_4131_ = v___x_4127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_map_u2082_4125_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4132_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_s_4134_: *mut leanh::LeanObject,
    mut v_e_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4136_ = leanh::lean_ctor_get(v_e_4135_, 0);
    leanh::lean_inc(v_name_4136_);
    v_info_4137_ = leanh::lean_ctor_get(v_e_4135_, 1);
    leanh::lean_inc_ref(v_info_4137_);
    leanh::lean_dec_ref(v_e_4135_);
    v___x_4138_ =
        l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(
            v_s_4134_,
            v_name_4136_,
            v_info_4137_,
        );
    return v___x_4138_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(
    mut v_00_u03b2_4139_: *mut leanh::LeanObject,
    mut v_x_4140_: *mut leanh::LeanObject,
    mut v_x_4141_: *mut leanh::LeanObject,
    mut v_x_4142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4143_ =
        l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(
            v_x_4140_, v_x_4141_, v_x_4142_,
        );
    return v___x_4143_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(
    mut v_00_u03b2_4144_: *mut leanh::LeanObject,
    mut v_x_4145_: *mut leanh::LeanObject,
    mut v_x_4146_: *mut leanh::LeanObject,
    mut v_x_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_x_4145_, v_x_4146_, v_x_4147_);
    return v___x_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(
    mut v_00_u03b2_4149_: *mut leanh::LeanObject,
    mut v_m_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
    mut v_b_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_m_4150_, v_a_4151_, v_b_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4154_: *mut leanh::LeanObject,
    mut v_x_4155_: *mut leanh::LeanObject,
    mut v_x_4156_: usize,
    mut v_x_4157_: usize,
    mut v_x_4158_: *mut leanh::LeanObject,
    mut v_x_4159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_4155_, v_x_4156_, v_x_4157_, v_x_4158_, v_x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4161_: *mut leanh::LeanObject,
    mut v_x_4162_: *mut leanh::LeanObject,
    mut v_x_4163_: *mut leanh::LeanObject,
    mut v_x_4164_: *mut leanh::LeanObject,
    mut v_x_4165_: *mut leanh::LeanObject,
    mut v_x_4166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1275__boxed_4167_: usize = 0;
    let mut v_x_1276__boxed_4168_: usize = 0;
    let mut v_res_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1275__boxed_4167_ = leanh::lean_unbox_usize(v_x_4163_);
    leanh::lean_dec(v_x_4163_);
    v_x_1276__boxed_4168_ = leanh::lean_unbox_usize(v_x_4164_);
    leanh::lean_dec(v_x_4164_);
    v_res_4169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_4161_, v_x_4162_, v_x_1275__boxed_4167_, v_x_1276__boxed_4168_, v_x_4165_, v_x_4166_);
    return v_res_4169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4170_: *mut leanh::LeanObject,
    mut v_a_4171_: *mut leanh::LeanObject,
    mut v_x_4172_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4173_: u8 = 0;
    v___x_4173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_4171_, v_x_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4174_: *mut leanh::LeanObject,
    mut v_a_4175_: *mut leanh::LeanObject,
    mut v_x_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4177_: u8 = 0;
    let mut v_r_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_4174_, v_a_4175_, v_x_4176_);
    leanh::lean_dec(v_x_4176_);
    leanh::lean_dec(v_a_4175_);
    v_r_4178_ = leanh::lean_box((v_res_4177_) as usize);
    return v_r_4178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4179_: *mut leanh::LeanObject,
    mut v_data_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_data_4180_);
    return v___x_4181_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_b_4184_: *mut leanh::LeanObject,
    mut v_x_4185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_4183_, v_b_4184_, v_x_4185_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4187_: *mut leanh::LeanObject,
    mut v_n_4188_: *mut leanh::LeanObject,
    mut v_k_4189_: *mut leanh::LeanObject,
    mut v_v_4190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4188_, v_k_4189_, v_v_4190_);
    return v___x_4191_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4192_: *mut leanh::LeanObject,
    mut v_depth_4193_: usize,
    mut v_keys_4194_: *mut leanh::LeanObject,
    mut v_vals_4195_: *mut leanh::LeanObject,
    mut v_heq_4196_: *mut leanh::LeanObject,
    mut v_i_4197_: *mut leanh::LeanObject,
    mut v_entries_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_4193_, v_keys_4194_, v_vals_4195_, v_i_4197_, v_entries_4198_);
    return v___x_4199_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4200_: *mut leanh::LeanObject,
    mut v_depth_4201_: *mut leanh::LeanObject,
    mut v_keys_4202_: *mut leanh::LeanObject,
    mut v_vals_4203_: *mut leanh::LeanObject,
    mut v_heq_4204_: *mut leanh::LeanObject,
    mut v_i_4205_: *mut leanh::LeanObject,
    mut v_entries_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4207_: usize = 0;
    let mut v_res_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4207_ = leanh::lean_unbox_usize(v_depth_4201_);
    leanh::lean_dec(v_depth_4201_);
    v_res_4208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4200_, v_depth_boxed_4207_, v_keys_4202_, v_vals_4203_, v_heq_4204_, v_i_4205_, v_entries_4206_);
    leanh::lean_dec_ref(v_vals_4203_);
    leanh::lean_dec_ref(v_keys_4202_);
    return v_res_4208_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_4209_: *mut leanh::LeanObject,
    mut v_i_4210_: *mut leanh::LeanObject,
    mut v_source_4211_: *mut leanh::LeanObject,
    mut v_target_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_4210_, v_source_4211_, v_target_4212_);
    return v___x_4213_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4214_: *mut leanh::LeanObject,
    mut v_x_4215_: *mut leanh::LeanObject,
    mut v_x_4216_: *mut leanh::LeanObject,
    mut v_x_4217_: *mut leanh::LeanObject,
    mut v_x_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4219_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4215_, v_x_4216_, v_x_4217_, v_x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_4220_: *mut leanh::LeanObject,
    mut v_x_4221_: *mut leanh::LeanObject,
    mut v_x_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_4221_, v_x_4222_);
    return v___x_4223_;
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
    mut v_m_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4225_: u8 = 0;
    let mut v_map_u2081_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4225_ = leanh::lean_ctor_get_uint8(
                    v_m_4224_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4225_ == 0 {
                    return v_m_4224_;
                } else {
                    v_map_u2081_4226_ = leanh::lean_ctor_get(v_m_4224_, 0);
                    v_map_u2082_4227_ = leanh::lean_ctor_get(v_m_4224_, 1);
                    v_isSharedCheck_4235_ = (!leanh::lean_is_exclusive(v_m_4224_)) as u8;
                    if v_isSharedCheck_4235_ == 0 {
                        v___x_4229_ = v_m_4224_;
                        v_isShared_4230_ = v_isSharedCheck_4235_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4227_);
                        leanh::lean_inc(v_map_u2081_4226_);
                        leanh::lean_dec(v_m_4224_);
                        v___x_4229_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4234_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_map_u2081_4226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_map_u2082_4227_);
                    v___x_4233_ = v_reuseFailAlloc_4234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4233_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4231_,
                );
                return v___x_4233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(
    mut v_00_u03b2_4236_: *mut leanh::LeanObject,
    mut v_m_4237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4238_ =
        l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
            v_m_4237_,
        );
    return v___x_4238_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_State_switch(
    mut v_s_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4240_ =
        l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(
            v_s_4239_,
        );
    return v___x_4240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(
    mut v_env_4241_: *mut leanh::LeanObject,
    mut v_as_4242_: *mut leanh::LeanObject,
    mut v_i_4243_: usize,
    mut v_stop_4244_: usize,
    mut v_b_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4251_ = lean_usize_dec_eq(v_i_4243_, v_stop_4244_);
                if v___x_4251_ == 0 {
                    v___x_4252_ = lean_array_uget_borrowed(v_as_4242_, v_i_4243_);
                    v_name_4253_ = leanh::lean_ctor_get(v___x_4252_, 0);
                    v___x_4254_ = 1;
                    leanh::lean_inc_ref(v_env_4241_);
                    v___x_4255_ = l_Lean_Environment_setExporting(v_env_4241_, v___x_4254_);
                    leanh::lean_inc(v_name_4253_);
                    v___x_4256_ =
                        l_Lean_Environment_contains(v___x_4255_, v_name_4253_, v___x_4251_);
                    if v___x_4256_ == 0 {
                        v___y_4247_ = v_b_4245_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_4252_);
                        v___x_4257_ = lean_array_push(v_b_4245_, v___x_4252_);
                        v___y_4247_ = v___x_4257_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4241_);
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
    mut v_env_4258_: *mut leanh::LeanObject,
    mut v_as_4259_: *mut leanh::LeanObject,
    mut v_i_4260_: *mut leanh::LeanObject,
    mut v_stop_4261_: *mut leanh::LeanObject,
    mut v_b_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4263_: usize = 0;
    let mut v_stop_boxed_4264_: usize = 0;
    let mut v_res_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4263_ = leanh::lean_unbox_usize(v_i_4260_);
    leanh::lean_dec(v_i_4260_);
    v_stop_boxed_4264_ = leanh::lean_unbox_usize(v_stop_4261_);
    leanh::lean_dec(v_stop_4261_);
    v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4258_, v_as_4259_, v_i_boxed_4263_, v_stop_boxed_4264_, v_b_4262_);
    leanh::lean_dec_ref(v_as_4259_);
    return v_res_4265_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_env_4268_: *mut leanh::LeanObject,
    mut v_x_4269_: *mut leanh::LeanObject,
    mut v_entries_4270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_all_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    v_all_4271_ = lean_array_mk(v_entries_4270_);
    v___x_4272_ = leanh::lean_unsigned_to_nat(0);
    v___x_4273_ = lean_array_get_size(v_all_4271_);
    v___x_4274_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_;
    v___x_4275_ = lean_nat_dec_lt(v___x_4272_, v___x_4273_);
    if v___x_4275_ == 0 {
        let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_4268_);
        v___x_4276_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_4276_, 0, v___x_4274_);
        leanh::lean_ctor_set(v___x_4276_, 1, v___x_4274_);
        leanh::lean_ctor_set(v___x_4276_, 2, v_all_4271_);
        return v___x_4276_;
    } else {
        let mut v___x_4277_: u8 = 0;
        v___x_4277_ = lean_nat_dec_le(v___x_4273_, v___x_4273_);
        if v___x_4277_ == 0 {
            if v___x_4275_ == 0 {
                let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_env_4268_);
                v___x_4278_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4278_, 0, v___x_4274_);
                leanh::lean_ctor_set(v___x_4278_, 1, v___x_4274_);
                leanh::lean_ctor_set(v___x_4278_, 2, v_all_4271_);
                return v___x_4278_;
            } else {
                let mut v___x_4279_: usize = 0;
                let mut v___x_4280_: usize = 0;
                let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4279_ = 0usize;
                v___x_4280_ = lean_usize_of_nat(v___x_4273_);
                v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4268_, v_all_4271_, v___x_4279_, v___x_4280_, v___x_4274_);
                leanh::lean_inc_ref(v___x_4281_);
                v___x_4282_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4282_, 0, v___x_4281_);
                leanh::lean_ctor_set(v___x_4282_, 1, v___x_4281_);
                leanh::lean_ctor_set(v___x_4282_, 2, v_all_4271_);
                return v___x_4282_;
            }
        } else {
            let mut v___x_4283_: usize = 0;
            let mut v___x_4284_: usize = 0;
            let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4283_ = 0usize;
            v___x_4284_ = lean_usize_of_nat(v___x_4273_);
            v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_4268_, v_all_4271_, v___x_4283_, v___x_4284_, v___x_4274_);
            leanh::lean_inc_ref(v___x_4285_);
            v___x_4286_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_4286_, 0, v___x_4285_);
            leanh::lean_ctor_set(v___x_4286_, 1, v___x_4285_);
            leanh::lean_ctor_set(v___x_4286_, 2, v_all_4271_);
            return v___x_4286_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(
    mut v_env_4287_: *mut leanh::LeanObject,
    mut v_x_4288_: *mut leanh::LeanObject,
    mut v_entries_4289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4290_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_env_4287_, v_x_4288_, v_entries_4289_);
    leanh::lean_dec_ref(v_x_4288_);
    return v_res_4290_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_es_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = lean_array_mk(v_es_4291_);
    return v___x_4292_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(
    mut v_as_4293_: *mut leanh::LeanObject,
    mut v_i_4294_: usize,
    mut v_stop_4295_: usize,
    mut v_b_4296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4297_: u8 = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: usize = 0;
    let mut v___x_4301_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4297_ = lean_usize_dec_eq(v_i_4294_, v_stop_4295_);
                if v___x_4297_ == 0 {
                    v___x_4298_ = lean_array_uget_borrowed(v_as_4293_, v_i_4294_);
                    leanh::lean_inc(v___x_4298_);
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
    mut v_as_4303_: *mut leanh::LeanObject,
    mut v_i_4304_: *mut leanh::LeanObject,
    mut v_stop_4305_: *mut leanh::LeanObject,
    mut v_b_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4307_: usize = 0;
    let mut v_stop_boxed_4308_: usize = 0;
    let mut v_res_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4307_ = leanh::lean_unbox_usize(v_i_4304_);
    leanh::lean_dec(v_i_4304_);
    v_stop_boxed_4308_ = leanh::lean_unbox_usize(v_stop_4305_);
    leanh::lean_dec(v_stop_4305_);
    v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v_as_4303_, v_i_boxed_4307_, v_stop_boxed_4308_, v_b_4306_);
    leanh::lean_dec_ref(v_as_4303_);
    return v_res_4309_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(
    mut v_as_4310_: *mut leanh::LeanObject,
    mut v_i_4311_: usize,
    mut v_stop_4312_: usize,
    mut v_b_4313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: usize = 0;
    let mut v___x_4317_: usize = 0;
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: usize = 0;
    let mut v___x_4326_: usize = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: usize = 0;
    let mut v___x_4329_: usize = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4319_ = lean_usize_dec_eq(v_i_4311_, v_stop_4312_);
                if v___x_4319_ == 0 {
                    v___x_4320_ = lean_array_uget_borrowed(v_as_4310_, v_i_4311_);
                    v___x_4321_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_as_4331_: *mut leanh::LeanObject,
    mut v_i_4332_: *mut leanh::LeanObject,
    mut v_stop_4333_: *mut leanh::LeanObject,
    mut v_b_4334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4335_: usize = 0;
    let mut v_stop_boxed_4336_: usize = 0;
    let mut v_res_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4335_ = leanh::lean_unbox_usize(v_i_4332_);
    leanh::lean_dec(v_i_4332_);
    v_stop_boxed_4336_ = leanh::lean_unbox_usize(v_stop_4333_);
    leanh::lean_dec(v_stop_4333_);
    v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4331_, v_i_boxed_4335_, v_stop_boxed_4336_, v_b_4334_);
    leanh::lean_dec_ref(v_as_4331_);
    return v_res_4337_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(
    mut v_initState_4338_: *mut leanh::LeanObject,
    mut v_as_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    v___x_4340_ = leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4344_ = 0usize;
                v___x_4345_ = lean_usize_of_nat(v___x_4341_);
                v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4339_, v___x_4344_, v___x_4345_, v_initState_4338_);
                return v___x_4346_;
            }
        } else {
            let mut v___x_4347_: usize = 0;
            let mut v___x_4348_: usize = 0;
            let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4347_ = 0usize;
            v___x_4348_ = lean_usize_of_nat(v___x_4341_);
            v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_4339_, v___x_4347_, v___x_4348_, v_initState_4338_);
            return v___x_4349_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(
    mut v_initState_4350_: *mut leanh::LeanObject,
    mut v_as_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v_initState_4350_, v_as_4351_);
    leanh::lean_dec_ref(v_as_4351_);
    return v_res_4352_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(
    mut v_es_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4354_ = leanh::lean_obj_once(
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
    mut v_es_4357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4358_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_es_4357_);
    leanh::lean_dec_ref(v_es_4357_);
    return v_res_4358_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_;
    v___x_4388_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(
    mut v_a_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
    return v_res_4390_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_addMatcherInfo(
    mut v_env_4391_: *mut leanh::LeanObject,
    mut v_matcherName_4392_: *mut leanh::LeanObject,
    mut v_info_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = l_Lean_Meta_Match_Extension_extension;
    v_toEnvExtension_4395_ = leanh::lean_ctor_get(v___x_4394_, 0);
    v_asyncMode_4396_ = leanh::lean_ctor_get(v_toEnvExtension_4395_, 2);
    leanh::lean_inc(v_matcherName_4392_);
    v___x_4397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4397_, 0, v_matcherName_4392_);
    leanh::lean_ctor_set(v___x_4397_, 1, v_info_4393_);
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
    mut v_keys_4399_: *mut leanh::LeanObject,
    mut v_vals_4400_: *mut leanh::LeanObject,
    mut v_i_4401_: *mut leanh::LeanObject,
    mut v_k_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4403_ = lean_array_get_size(v_keys_4399_);
                v___x_4404_ = lean_nat_dec_lt(v_i_4401_, v___x_4403_);
                if v___x_4404_ == 0 {
                    leanh::lean_dec(v_i_4401_);
                    v___x_4405_ = leanh::lean_box(0);
                    return v___x_4405_;
                } else {
                    v_k_x27_4406_ = lean_array_fget_borrowed(v_keys_4399_, v_i_4401_);
                    v___x_4407_ = lean_name_eq(v_k_4402_, v_k_x27_4406_);
                    if v___x_4407_ == 0 {
                        v___x_4408_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4409_ = lean_nat_add(v_i_4401_, v___x_4408_);
                        leanh::lean_dec(v_i_4401_);
                        v_i_4401_ = v___x_4409_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4411_ = lean_array_fget_borrowed(v_vals_4400_, v_i_4401_);
                        leanh::lean_dec(v_i_4401_);
                        leanh::lean_inc(v___x_4411_);
                        v___x_4412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4412_, 0, v___x_4411_);
                        return v___x_4412_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_4413_: *mut leanh::LeanObject,
    mut v_vals_4414_: *mut leanh::LeanObject,
    mut v_i_4415_: *mut leanh::LeanObject,
    mut v_k_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4413_, v_vals_4414_, v_i_4415_, v_k_4416_);
    leanh::lean_dec(v_k_4416_);
    leanh::lean_dec_ref(v_vals_4414_);
    leanh::lean_dec_ref(v_keys_4413_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_4418_: *mut leanh::LeanObject,
    mut v_x_4419_: usize,
    mut v_x_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: usize = 0;
    let mut v___x_4424_: usize = 0;
    let mut v___x_4425_: usize = 0;
    let mut v_j_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: usize = 0;
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4418_) == 0 {
                    v_es_4421_ = leanh::lean_ctor_get(v_x_4418_, 0);
                    v___x_4422_ = leanh::lean_box(2);
                    v___x_4423_ = 5usize;
                    v___x_4424_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4425_ = lean_usize_land(v_x_4419_, v___x_4424_);
                    v_j_4426_ = lean_usize_to_nat(v___x_4425_);
                    v___x_4427_ = lean_array_get_borrowed(v___x_4422_, v_es_4421_, v_j_4426_);
                    leanh::lean_dec(v_j_4426_);
                    match leanh::lean_obj_tag(v___x_4427_) {
                        0 => {
                            v_key_4428_ = leanh::lean_ctor_get(v___x_4427_, 0);
                            v_val_4429_ = leanh::lean_ctor_get(v___x_4427_, 1);
                            v___x_4430_ = lean_name_eq(v_x_4420_, v_key_4428_);
                            if v___x_4430_ == 0 {
                                v___x_4431_ = leanh::lean_box(0);
                                return v___x_4431_;
                            } else {
                                leanh::lean_inc(v_val_4429_);
                                v___x_4432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4432_, 0, v_val_4429_);
                                return v___x_4432_;
                            }
                        }
                        1 => {
                            v_node_4433_ = leanh::lean_ctor_get(v___x_4427_, 0);
                            v___x_4434_ = lean_usize_shift_right(v_x_4419_, v___x_4423_);
                            v_x_4418_ = v_node_4433_;
                            v_x_4419_ = v___x_4434_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4436_ = leanh::lean_box(0);
                            return v___x_4436_;
                        }
                    }
                } else {
                    v_ks_4437_ = leanh::lean_ctor_get(v_x_4418_, 0);
                    v_vs_4438_ = leanh::lean_ctor_get(v_x_4418_, 1);
                    v___x_4439_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4437_, v_vs_4438_, v___x_4439_, v_x_4420_);
                    return v___x_4440_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4441_: *mut leanh::LeanObject,
    mut v_x_4442_: *mut leanh::LeanObject,
    mut v_x_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_573__boxed_4444_: usize = 0;
    let mut v_res_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_573__boxed_4444_ = leanh::lean_unbox_usize(v_x_4442_);
    leanh::lean_dec(v_x_4442_);
    v_res_4445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_4441_, v_x_573__boxed_4444_, v_x_4443_);
    leanh::lean_dec(v_x_4443_);
    leanh::lean_dec_ref(v_x_4441_);
    return v_res_4445_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(
    mut v_x_4446_: *mut leanh::LeanObject,
    mut v_x_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4449_: u64 = 0;
    let mut v___x_4450_: usize = 0;
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u64 = 0;
    let mut v_hash_4453_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4447_) == 0 {
                    v___x_4452_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4449_ = v___x_4452_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4453_ = leanh::lean_ctor_get_uint64(
                        v_x_4447_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_4454_: *mut leanh::LeanObject,
    mut v_x_4455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_4454_, v_x_4455_);
    leanh::lean_dec(v_x_4455_);
    leanh::lean_dec_ref(v_x_4454_);
    return v_res_4456_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(
    mut v_a_4457_: *mut leanh::LeanObject,
    mut v_x_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4458_) == 0 {
                    v___x_4459_ = leanh::lean_box(0);
                    return v___x_4459_;
                } else {
                    v_key_4460_ = leanh::lean_ctor_get(v_x_4458_, 0);
                    v_value_4461_ = leanh::lean_ctor_get(v_x_4458_, 1);
                    v_tail_4462_ = leanh::lean_ctor_get(v_x_4458_, 2);
                    v___x_4463_ = lean_name_eq(v_key_4460_, v_a_4457_);
                    if v___x_4463_ == 0 {
                        v_x_4458_ = v_tail_4462_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4461_);
                        v___x_4465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4465_, 0, v_value_4461_);
                        return v___x_4465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_4466_: *mut leanh::LeanObject,
    mut v_x_4467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_4466_, v_x_4467_);
    leanh::lean_dec(v_x_4467_);
    leanh::lean_dec(v_a_4466_);
    return v_res_4468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(
    mut v_m_4469_: *mut leanh::LeanObject,
    mut v_a_4470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: u64 = 0;
    let mut v_hash_4489_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4471_ = leanh::lean_ctor_get(v_m_4469_, 1);
                v___x_4472_ = lean_array_get_size(v_buckets_4471_);
                if leanh::lean_obj_tag(v_a_4470_) == 0 {
                    v___x_4488_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
                    v___y_4474_ = v___x_4488_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4489_ = leanh::lean_ctor_get_uint64(
                        v_a_4470_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_4490_: *mut leanh::LeanObject,
    mut v_a_4491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_4490_, v_a_4491_);
    leanh::lean_dec(v_a_4491_);
    leanh::lean_dec_ref(v_m_4490_);
    return v_res_4492_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
    mut v_x_4493_: *mut leanh::LeanObject,
    mut v_x_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4495_: u8 = 0;
    v_stage_u2081_4495_ = leanh::lean_ctor_get_uint8(
        v_x_4493_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4495_ == 0 {
        let mut v_map_u2081_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4496_ = leanh::lean_ctor_get(v_x_4493_, 0);
        v_map_u2082_4497_ = leanh::lean_ctor_get(v_x_4493_, 1);
        v___x_4498_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_4497_, v_x_4494_);
        if leanh::lean_obj_tag(v___x_4498_) == 0 {
            let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_4496_, v_x_4494_);
            return v___x_4499_;
        } else {
            return v___x_4498_;
        }
    } else {
        let mut v_map_u2081_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4500_ = leanh::lean_ctor_get(v_x_4493_, 0);
        v___x_4501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_4500_, v_x_4494_);
        return v___x_4501_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(
    mut v_x_4502_: *mut leanh::LeanObject,
    mut v_x_4503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4504_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
            v_x_4502_, v_x_4503_,
        );
    leanh::lean_dec(v_x_4503_);
    leanh::lean_dec_ref(v_x_4502_);
    return v_res_4504_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4506_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0;
    v___x_4507_ = lean_string_utf8_byte_size(v___x_4506_);
    return v___x_4507_;
}
pub unsafe fn l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(
    mut v_env_4508_: *mut leanh::LeanObject,
    mut v_declName_4509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_4509_);
    v___x_4510_ = lean_erase_macro_scopes(v_declName_4509_);
    if leanh::lean_obj_tag(v___x_4510_) == 1 {
        let mut v_str_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4515_: u8 = 0;
        v_str_4511_ = leanh::lean_ctor_get(v___x_4510_, 1);
        leanh::lean_inc_ref(v_str_4511_);
        leanh::lean_dec_ref_known(v___x_4510_, 2);
        v___x_4512_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0;
        v___x_4513_ = lean_string_utf8_byte_size(v_str_4511_);
        v___x_4514_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once
            ),
            _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1,
        );
        v___x_4515_ = lean_nat_dec_le(v___x_4514_, v___x_4513_);
        if v___x_4515_ == 0 {
            let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_str_4511_);
            leanh::lean_dec(v_declName_4509_);
            leanh::lean_dec_ref(v_env_4508_);
            v___x_4516_ = leanh::lean_box(0);
            return v___x_4516_;
        } else {
            let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4518_: u8 = 0;
            v___x_4517_ = leanh::lean_unsigned_to_nat(0);
            v___x_4518_ = lean_string_memcmp(
                v_str_4511_,
                v___x_4512_,
                v___x_4517_,
                v___x_4517_,
                v___x_4514_,
            );
            leanh::lean_dec_ref(v_str_4511_);
            if v___x_4518_ == 0 {
                let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_declName_4509_);
                leanh::lean_dec_ref(v_env_4508_);
                v___x_4519_ = leanh::lean_box(0);
                return v___x_4519_;
            } else {
                let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_toEnvExtension_4521_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_asyncMode_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4520_ = l_Lean_Meta_Match_Extension_extension;
                v_toEnvExtension_4521_ = leanh::lean_ctor_get(v___x_4520_, 0);
                v_asyncMode_4522_ = leanh::lean_ctor_get(v_toEnvExtension_4521_, 2);
                v___x_4523_ = l_Lean_Meta_Match_Extension_instInhabitedState;
                leanh::lean_inc(v_declName_4509_);
                v___x_4524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4523_,
                    v___x_4520_,
                    v_env_4508_,
                    v_asyncMode_4522_,
                    v_declName_4509_,
                );
                v___x_4525_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_4524_, v_declName_4509_);
                leanh::lean_dec(v_declName_4509_);
                leanh::lean_dec(v___x_4524_);
                return v___x_4525_;
            }
        }
    } else {
        let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4510_);
        leanh::lean_dec(v_declName_4509_);
        leanh::lean_dec_ref(v_env_4508_);
        v___x_4526_ = leanh::lean_box(0);
        return v___x_4526_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(
    mut v_00_u03b2_4527_: *mut leanh::LeanObject,
    mut v_x_4528_: *mut leanh::LeanObject,
    mut v_x_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4530_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(
            v_x_4528_, v_x_4529_,
        );
    return v___x_4530_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(
    mut v_00_u03b2_4531_: *mut leanh::LeanObject,
    mut v_x_4532_: *mut leanh::LeanObject,
    mut v_x_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4534_ =
        l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(
            v_00_u03b2_4531_,
            v_x_4532_,
            v_x_4533_,
        );
    leanh::lean_dec(v_x_4533_);
    leanh::lean_dec_ref(v_x_4532_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(
    mut v_00_u03b2_4535_: *mut leanh::LeanObject,
    mut v_x_4536_: *mut leanh::LeanObject,
    mut v_x_4537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_4536_, v_x_4537_);
    return v___x_4538_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4539_: *mut leanh::LeanObject,
    mut v_x_4540_: *mut leanh::LeanObject,
    mut v_x_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_4539_, v_x_4540_, v_x_4541_);
    leanh::lean_dec(v_x_4541_);
    leanh::lean_dec_ref(v_x_4540_);
    return v_res_4542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(
    mut v_00_u03b2_4543_: *mut leanh::LeanObject,
    mut v_m_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_4544_, v_a_4545_);
    return v___x_4546_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(
    mut v_00_u03b2_4547_: *mut leanh::LeanObject,
    mut v_m_4548_: *mut leanh::LeanObject,
    mut v_a_4549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_4547_, v_m_4548_, v_a_4549_);
    leanh::lean_dec(v_a_4549_);
    leanh::lean_dec_ref(v_m_4548_);
    return v_res_4550_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4551_: *mut leanh::LeanObject,
    mut v_x_4552_: *mut leanh::LeanObject,
    mut v_x_4553_: usize,
    mut v_x_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_4552_, v_x_4553_, v_x_4554_);
    return v___x_4555_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4556_: *mut leanh::LeanObject,
    mut v_x_4557_: *mut leanh::LeanObject,
    mut v_x_4558_: *mut leanh::LeanObject,
    mut v_x_4559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_775__boxed_4560_: usize = 0;
    let mut v_res_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_775__boxed_4560_ = leanh::lean_unbox_usize(v_x_4558_);
    leanh::lean_dec(v_x_4558_);
    v_res_4561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4556_, v_x_4557_, v_x_775__boxed_4560_, v_x_4559_);
    leanh::lean_dec(v_x_4559_);
    leanh::lean_dec_ref(v_x_4557_);
    return v_res_4561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
    mut v_x_4564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4565_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_4563_, v_x_4564_);
    return v___x_4565_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
    mut v_x_4568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_4566_, v_a_4567_, v_x_4568_);
    leanh::lean_dec(v_x_4568_);
    leanh::lean_dec(v_a_4567_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4570_: *mut leanh::LeanObject,
    mut v_keys_4571_: *mut leanh::LeanObject,
    mut v_vals_4572_: *mut leanh::LeanObject,
    mut v_heq_4573_: *mut leanh::LeanObject,
    mut v_i_4574_: *mut leanh::LeanObject,
    mut v_k_4575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4576_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4571_, v_vals_4572_, v_i_4574_, v_k_4575_);
    return v___x_4576_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4577_: *mut leanh::LeanObject,
    mut v_keys_4578_: *mut leanh::LeanObject,
    mut v_vals_4579_: *mut leanh::LeanObject,
    mut v_heq_4580_: *mut leanh::LeanObject,
    mut v_i_4581_: *mut leanh::LeanObject,
    mut v_k_4582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4583_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4577_, v_keys_4578_, v_vals_4579_, v_heq_4580_, v_i_4581_, v_k_4582_);
    leanh::lean_dec(v_k_4582_);
    leanh::lean_dec_ref(v_vals_4579_);
    leanh::lean_dec_ref(v_keys_4578_);
    return v_res_4583_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(
    mut v_matcherName_4584_: *mut leanh::LeanObject,
    mut v_info_4585_: *mut leanh::LeanObject,
    mut v_env_4586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4587_ =
        l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_4586_, v_matcherName_4584_, v_info_4585_);
    return v___x_4587_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___redArg(
    mut v_inst_4588_: *mut leanh::LeanObject,
    mut v_matcherName_4589_: *mut leanh::LeanObject,
    mut v_info_4590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyEnv_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_4591_ = leanh::lean_ctor_get(v_inst_4588_, 1);
    leanh::lean_inc(v_modifyEnv_4591_);
    leanh::lean_dec_ref(v_inst_4588_);
    v___f_4592_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4592_, 0, v_matcherName_4589_);
    leanh::lean_closure_set(v___f_4592_, 1, v_info_4590_);
    v___x_4593_ = leanh::lean_apply_1(v_modifyEnv_4591_, v___f_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo(
    mut v_m_4594_: *mut leanh::LeanObject,
    mut v_inst_4595_: *mut leanh::LeanObject,
    mut v_inst_4596_: *mut leanh::LeanObject,
    mut v_matcherName_4597_: *mut leanh::LeanObject,
    mut v_info_4598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ =
        l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_4596_, v_matcherName_4597_, v_info_4598_);
    return v___x_4599_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___boxed(
    mut v_m_4600_: *mut leanh::LeanObject,
    mut v_inst_4601_: *mut leanh::LeanObject,
    mut v_inst_4602_: *mut leanh::LeanObject,
    mut v_matcherName_4603_: *mut leanh::LeanObject,
    mut v_info_4604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4605_ = l_Lean_Meta_Match_addMatcherInfo(
        v_m_4600_,
        v_inst_4601_,
        v_inst_4602_,
        v_matcherName_4603_,
        v_info_4604_,
    );
    leanh::lean_dec_ref(v_inst_4601_);
    return v_res_4605_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfoCore_x3f(
    mut v_env_4606_: *mut leanh::LeanObject,
    mut v_declName_4607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4606_, v_declName_4607_);
    return v___x_4608_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(
    mut v_declName_4609_: *mut leanh::LeanObject,
    mut v_toPure_4610_: *mut leanh::LeanObject,
    mut v_____do__lift_4611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4612_ =
        l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_4611_, v_declName_4609_);
    v___x_4613_ =
        leanh::lean_apply_2(v_toPure_4610_, leanh::lean_box(0), v___x_4612_);
    return v___x_4613_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___redArg(
    mut v_inst_4614_: *mut leanh::LeanObject,
    mut v_inst_4615_: *mut leanh::LeanObject,
    mut v_declName_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4617_ = leanh::lean_ctor_get(v_inst_4614_, 0);
    leanh::lean_inc_ref(v_toApplicative_4617_);
    v_toBind_4618_ = leanh::lean_ctor_get(v_inst_4614_, 1);
    leanh::lean_inc(v_toBind_4618_);
    leanh::lean_dec_ref(v_inst_4614_);
    v_getEnv_4619_ = leanh::lean_ctor_get(v_inst_4615_, 0);
    leanh::lean_inc(v_getEnv_4619_);
    leanh::lean_dec_ref(v_inst_4615_);
    v_toPure_4620_ = leanh::lean_ctor_get(v_toApplicative_4617_, 1);
    leanh::lean_inc(v_toPure_4620_);
    leanh::lean_dec_ref(v_toApplicative_4617_);
    v___f_4621_ = leanh::lean_alloc_closure(
        l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4621_, 0, v_declName_4616_);
    leanh::lean_closure_set(v___f_4621_, 1, v_toPure_4620_);
    v___x_4622_ = leanh::lean_apply_4(
        v_toBind_4618_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4619_,
        v___f_4621_,
    );
    return v___x_4622_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f(
    mut v_m_4623_: *mut leanh::LeanObject,
    mut v_inst_4624_: *mut leanh::LeanObject,
    mut v_inst_4625_: *mut leanh::LeanObject,
    mut v_declName_4626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ =
        l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4624_, v_inst_4625_, v_declName_4626_);
    return v___x_4627_;
}
pub unsafe fn lean_is_matcher(
    mut v_env_4628_: *mut leanh::LeanObject,
    mut v_declName_4629_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4628_, v_declName_4629_);
    if leanh::lean_obj_tag(v___x_4630_) == 0 {
        let mut v___x_4631_: u8 = 0;
        v___x_4631_ = 0;
        return v___x_4631_;
    } else {
        let mut v___x_4632_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_4630_, 1);
        v___x_4632_ = 1;
        return v___x_4632_;
    }
}
pub unsafe fn l_Lean_Meta_isMatcherCore___boxed(
    mut v_env_4633_: *mut leanh::LeanObject,
    mut v_declName_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4635_: u8 = 0;
    let mut v_r_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4635_ = lean_is_matcher(v_env_4633_, v_declName_4634_);
    v_r_4636_ = leanh::lean_box((v_res_4635_) as usize);
    return v_r_4636_;
}
pub unsafe fn l_Lean_Meta_isMatcher___redArg___lam__0(
    mut v_declName_4637_: *mut leanh::LeanObject,
    mut v_toPure_4638_: *mut leanh::LeanObject,
    mut v_____do__lift_4639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4640_ = lean_is_matcher(v_____do__lift_4639_, v_declName_4637_);
    v___x_4641_ = leanh::lean_box((v___x_4640_) as usize);
    v___x_4642_ =
        leanh::lean_apply_2(v_toPure_4638_, leanh::lean_box(0), v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Lean_Meta_isMatcher___redArg(
    mut v_inst_4643_: *mut leanh::LeanObject,
    mut v_inst_4644_: *mut leanh::LeanObject,
    mut v_declName_4645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4646_ = leanh::lean_ctor_get(v_inst_4643_, 0);
    leanh::lean_inc_ref(v_toApplicative_4646_);
    v_toBind_4647_ = leanh::lean_ctor_get(v_inst_4643_, 1);
    leanh::lean_inc(v_toBind_4647_);
    leanh::lean_dec_ref(v_inst_4643_);
    v_getEnv_4648_ = leanh::lean_ctor_get(v_inst_4644_, 0);
    leanh::lean_inc(v_getEnv_4648_);
    leanh::lean_dec_ref(v_inst_4644_);
    v_toPure_4649_ = leanh::lean_ctor_get(v_toApplicative_4646_, 1);
    leanh::lean_inc(v_toPure_4649_);
    leanh::lean_dec_ref(v_toApplicative_4646_);
    v___f_4650_ = leanh::lean_alloc_closure(
        l_Lean_Meta_isMatcher___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4650_, 0, v_declName_4645_);
    leanh::lean_closure_set(v___f_4650_, 1, v_toPure_4649_);
    v___x_4651_ = leanh::lean_apply_4(
        v_toBind_4647_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4648_,
        v___f_4650_,
    );
    return v___x_4651_;
}
pub unsafe fn l_Lean_Meta_isMatcher(
    mut v_m_4652_: *mut leanh::LeanObject,
    mut v_inst_4653_: *mut leanh::LeanObject,
    mut v_inst_4654_: *mut leanh::LeanObject,
    mut v_declName_4655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4656_ = l_Lean_Meta_isMatcher___redArg(v_inst_4653_, v_inst_4654_, v_declName_4655_);
    return v___x_4656_;
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore_x3f(
    mut v_env_4657_: *mut leanh::LeanObject,
    mut v_e_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    v_fn_4659_ = l_Lean_Expr_getAppFn(v_e_4658_);
    v___x_4660_ = l_Lean_Expr_isConst(v_fn_4659_);
    if v___x_4660_ == 0 {
        let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_fn_4659_);
        leanh::lean_dec_ref(v_env_4657_);
        v___x_4661_ = leanh::lean_box(0);
        return v___x_4661_;
    } else {
        let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4662_ = l_Lean_Expr_constName_x21(v_fn_4659_);
        leanh::lean_dec_ref(v_fn_4659_);
        v___x_4663_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4657_, v___x_4662_);
        if leanh::lean_obj_tag(v___x_4663_) == 1 {
            let mut v_val_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4667_: u8 = 0;
            v_val_4664_ = leanh::lean_ctor_get(v___x_4663_, 0);
            leanh::lean_inc(v_val_4664_);
            v___x_4665_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_4664_);
            leanh::lean_dec(v_val_4664_);
            v___x_4666_ = l_Lean_Expr_getAppNumArgs(v_e_4658_);
            v___x_4667_ = lean_nat_dec_le(v___x_4665_, v___x_4666_);
            leanh::lean_dec(v___x_4666_);
            leanh::lean_dec(v___x_4665_);
            if v___x_4667_ == 0 {
                let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_4663_, 1);
                v___x_4668_ = leanh::lean_box(0);
                return v___x_4668_;
            } else {
                return v___x_4663_;
            }
        } else {
            let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4663_);
            v___x_4669_ = leanh::lean_box(0);
            return v___x_4669_;
        }
    }
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore_x3f___boxed(
    mut v_env_4670_: *mut leanh::LeanObject,
    mut v_e_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_4670_, v_e_4671_);
    leanh::lean_dec_ref(v_e_4671_);
    return v_res_4672_;
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore(
    mut v_env_4673_: *mut leanh::LeanObject,
    mut v_e_4674_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4675_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_4673_, v_e_4674_);
    if leanh::lean_obj_tag(v___x_4675_) == 0 {
        let mut v___x_4676_: u8 = 0;
        v___x_4676_ = 0;
        return v___x_4676_;
    } else {
        let mut v___x_4677_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_4675_, 1);
        v___x_4677_ = 1;
        return v___x_4677_;
    }
}
pub unsafe fn l_Lean_Meta_isMatcherAppCore___boxed(
    mut v_env_4678_: *mut leanh::LeanObject,
    mut v_e_4679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4680_: u8 = 0;
    let mut v_r_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Lean_Meta_isMatcherAppCore(v_env_4678_, v_e_4679_);
    leanh::lean_dec_ref(v_e_4679_);
    v_r_4681_ = leanh::lean_box((v_res_4680_) as usize);
    return v_r_4681_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg___lam__0(
    mut v_e_4682_: *mut leanh::LeanObject,
    mut v_toPure_4683_: *mut leanh::LeanObject,
    mut v_____do__lift_4684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4685_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_4684_, v_e_4682_);
    v___x_4686_ = leanh::lean_box((v___x_4685_) as usize);
    v___x_4687_ =
        leanh::lean_apply_2(v_toPure_4683_, leanh::lean_box(0), v___x_4686_);
    return v___x_4687_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(
    mut v_e_4688_: *mut leanh::LeanObject,
    mut v_toPure_4689_: *mut leanh::LeanObject,
    mut v_____do__lift_4690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_4688_, v_toPure_4689_, v_____do__lift_4690_);
    leanh::lean_dec_ref(v_e_4688_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___redArg(
    mut v_inst_4692_: *mut leanh::LeanObject,
    mut v_inst_4693_: *mut leanh::LeanObject,
    mut v_e_4694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4695_ = leanh::lean_ctor_get(v_inst_4692_, 0);
    leanh::lean_inc_ref(v_toApplicative_4695_);
    v_toBind_4696_ = leanh::lean_ctor_get(v_inst_4692_, 1);
    leanh::lean_inc(v_toBind_4696_);
    leanh::lean_dec_ref(v_inst_4692_);
    v_getEnv_4697_ = leanh::lean_ctor_get(v_inst_4693_, 0);
    leanh::lean_inc(v_getEnv_4697_);
    leanh::lean_dec_ref(v_inst_4693_);
    v_toPure_4698_ = leanh::lean_ctor_get(v_toApplicative_4695_, 1);
    leanh::lean_inc(v_toPure_4698_);
    leanh::lean_dec_ref(v_toApplicative_4695_);
    v___f_4699_ = leanh::lean_alloc_closure(
        l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4699_, 0, v_e_4694_);
    leanh::lean_closure_set(v___f_4699_, 1, v_toPure_4698_);
    v___x_4700_ = leanh::lean_apply_4(
        v_toBind_4696_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4697_,
        v___f_4699_,
    );
    return v___x_4700_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp(
    mut v_m_4701_: *mut leanh::LeanObject,
    mut v_inst_4702_: *mut leanh::LeanObject,
    mut v_inst_4703_: *mut leanh::LeanObject,
    mut v_e_4704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_4702_, v_inst_4703_, v_e_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4712_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_;
    v___x_4713_ = leanh::lean_box(0);
    v___x_4714_ = l_Lean_mkTagDeclarationExtension(v___x_4712_, v___x_4713_);
    return v___x_4714_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(
    mut v_a_4715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
    return v_res_4716_;
}
pub unsafe fn l_Lean_Meta_markMatcherLike(
    mut v_env_4717_: *mut leanh::LeanObject,
    mut v_declName_4718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Lean_Meta_matcherLikeExt;
    v___x_4720_ = l_Lean_TagDeclarationExtension_tag(v___x_4719_, v_env_4717_, v_declName_4718_);
    return v___x_4720_;
}
pub unsafe fn l_Lean_Meta_isMatcherLikeCore(
    mut v_env_4721_: *mut leanh::LeanObject,
    mut v_declName_4722_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: u8 = 0;
    v___x_4723_ = l_Lean_Meta_matcherLikeExt;
    v_toEnvExtension_4724_ = leanh::lean_ctor_get(v___x_4723_, 0);
    v_asyncMode_4725_ = leanh::lean_ctor_get(v_toEnvExtension_4724_, 2);
    v___x_4726_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_4723_,
        v_env_4721_,
        v_declName_4722_,
        v_asyncMode_4725_,
    );
    return v___x_4726_;
}
pub unsafe fn l_Lean_Meta_isMatcherLikeCore___boxed(
    mut v_env_4727_: *mut leanh::LeanObject,
    mut v_declName_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4729_: u8 = 0;
    let mut v_r_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Lean_Meta_isMatcherLikeCore(v_env_4727_, v_declName_4728_);
    v_r_4730_ = leanh::lean_box((v_res_4729_) as usize);
    return v_r_4730_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___redArg___lam__0(
    mut v_declName_4731_: *mut leanh::LeanObject,
    mut v_toPure_4732_: *mut leanh::LeanObject,
    mut v_____do__lift_4733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4734_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_4733_, v_declName_4731_);
    v___x_4735_ = leanh::lean_box((v___x_4734_) as usize);
    v___x_4736_ =
        leanh::lean_apply_2(v_toPure_4732_, leanh::lean_box(0), v___x_4735_);
    return v___x_4736_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___redArg(
    mut v_inst_4737_: *mut leanh::LeanObject,
    mut v_inst_4738_: *mut leanh::LeanObject,
    mut v_declName_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4740_ = leanh::lean_ctor_get(v_inst_4737_, 0);
    leanh::lean_inc_ref(v_toApplicative_4740_);
    v_toBind_4741_ = leanh::lean_ctor_get(v_inst_4737_, 1);
    leanh::lean_inc(v_toBind_4741_);
    leanh::lean_dec_ref(v_inst_4737_);
    v_getEnv_4742_ = leanh::lean_ctor_get(v_inst_4738_, 0);
    leanh::lean_inc(v_getEnv_4742_);
    leanh::lean_dec_ref(v_inst_4738_);
    v_toPure_4743_ = leanh::lean_ctor_get(v_toApplicative_4740_, 1);
    leanh::lean_inc(v_toPure_4743_);
    leanh::lean_dec_ref(v_toApplicative_4740_);
    v___f_4744_ = leanh::lean_alloc_closure(
        l_Lean_Meta_isMatcherLike___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4744_, 0, v_declName_4739_);
    leanh::lean_closure_set(v___f_4744_, 1, v_toPure_4743_);
    v___x_4745_ = leanh::lean_apply_4(
        v_toBind_4741_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4742_,
        v___f_4744_,
    );
    return v___x_4745_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike(
    mut v_m_4746_: *mut leanh::LeanObject,
    mut v_inst_4747_: *mut leanh::LeanObject,
    mut v_inst_4748_: *mut leanh::LeanObject,
    mut v_declName_4749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_4747_, v_inst_4748_, v_declName_4749_);
    return v___x_4750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatcherInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Match_instInhabitedDiscrInfo_default =
        _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo_default);
    l_Lean_Meta_Match_instInhabitedDiscrInfo = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo);
    l_Lean_Meta_Match_instInhabitedOverlaps_default =
        _init_l_Lean_Meta_Match_instInhabitedOverlaps_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps_default);
    l_Lean_Meta_Match_instInhabitedOverlaps = _init_l_Lean_Meta_Match_instInhabitedOverlaps();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps);
    l_Lean_Meta_Match_instInhabitedMatcherInfo_default =
        _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo_default);
    l_Lean_Meta_Match_instInhabitedMatcherInfo = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo);
    l_Lean_Meta_Match_Extension_instInhabitedState =
        _init_l_Lean_Meta_Match_Extension_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_Extension_instInhabitedState);
    res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Match_Extension_extension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Match_Extension_extension);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_matcherLikeExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_matcherLikeExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatcherInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_MatcherInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatcherInfo(builtin);
}