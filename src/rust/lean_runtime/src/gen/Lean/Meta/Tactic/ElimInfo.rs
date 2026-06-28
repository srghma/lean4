// Lean compiler output
// Module: Lean.Meta.Tactic.ElimInfo
// Imports: Lean.Meta.Check Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Array::Basic::l_Array_takeWhile___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_Expr_const___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar,
    l_Lean_Expr_headBeta, l_Lean_Expr_isFVar, l_Lean_Expr_isFVar___boxed, l_Lean_Expr_isSort,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override, l_Lean_instBEqFVarId_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_instReprExpr_repr,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getDecl___redArg, l_Lean_MVarId_getDecl, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg,
    runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::MetavarContext::{
    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{lean_expr_eqv, lean_expr_instantiate1};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_7, lean_box, lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value: LeanStringObject<2> =
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
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 63, 0],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value: LeanStringObject<10> =
    LeanStringObject {
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
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value: LeanStringObject<13> =
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
        m_data: [112, 114, 111, 118, 101, 115, 77, 111, 116, 105, 118, 101, 0],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value: LeanStringObject<3> =
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
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimAltInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprElimAltInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprElimAltInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprElimAltInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedElimAltInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedElimAltInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value:
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
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value:
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
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [101, 108, 105, 109, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value: LeanStringObject<9> =
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
        m_data: [101, 108, 105, 109, 84, 121, 112, 101, 0],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [109, 111, 116, 105, 118, 101, 80, 111, 115, 0],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value: LeanStringObject<11> =
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
        m_data: [116, 97, 114, 103, 101, 116, 115, 80, 111, 115, 0],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value: LeanStringObject<9> =
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
        m_data: [97, 108, 116, 115, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value: LeanStringObject<21> =
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
            110, 117, 109, 67, 111, 109, 112, 108, 101, 120, 77, 111, 116, 105, 118, 101, 65, 114,
            103, 115, 0,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprElimInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprElimInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprElimInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprElimInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprElimInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value: LeanStringObject<20> =
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
            95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109,
            121, 0,
        ],
    };
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value)
                as *mut LeanObject,
            17542774118954891045 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedElimInfo_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedElimInfo_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedElimInfo: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [77, 111, 116, 105, 118, 101, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 32, 115, 111, 114, 116, 44, 32, 110, 111, 116, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 116, 32, 109, 111, 116, 105, 118, 101, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 116, 121, 112, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value:
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
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value:
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
    m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value:
    LeanStringObject<108> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 108,
    m_capacity: 108,
    m_length: 107,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32,
        116, 121, 112, 101, 32, 111, 102, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32,
        116, 111, 32, 98, 101, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110,
        32, 111, 102, 32, 111, 110, 101, 32, 111, 102, 32, 105, 116, 115, 32, 112, 97, 114, 97,
        109, 101, 116, 101, 114, 115, 32, 40, 116, 104, 101, 32, 109, 111, 116, 105, 118, 101, 41,
        44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 0,
    ],
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getElimExprInfo___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value:
    LeanStringObject<1> = LeanStringObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_getElimExprInfo___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Meta_getElimExprInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_getElimExprInfo___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_getElimExprInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__0_value) as *mut LeanObject,
        12843180897352504333 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_getElimExprInfo___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__1_value) as *mut LeanObject,
        2883730740379873696 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_getElimExprInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_getElimExprInfo___closed__3_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_getElimExprInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_getElimExprInfo___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__3_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_getElimExprInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_getElimExprInfo___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getElimExprInfo___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getElimExprInfo___closed__6_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 0],
};
static mut l_Lean_Meta_getElimExprInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_getElimExprInfo___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getElimExprInfo___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getElimExprInfo___closed__8_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [10, 104, 97, 115, 32, 116, 121, 112, 101, 0],
};
static mut l_Lean_Meta_getElimExprInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__8_value) as *mut LeanObject;
static mut l_Lean_Meta_getElimExprInfo___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getElimExprInfo___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 116, 97, 114, 103, 101, 116, 58, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [73, 110, 115, 117, 102, 102, 105, 99, 105, 101, 110, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116, 97, 114, 103, 101, 116, 115, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [84, 111, 111, 32, 109, 97, 110, 121, 32, 116, 97, 114, 103, 101, 116, 115, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 102, 101, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 102, 101, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 116, 97, 114, 103, 101, 116, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_addImplicitTargets___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_addImplicitTargets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addImplicitTargets___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedCustomEliminator_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedCustomEliminator: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_getElimExprInfo___closed__1_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value: LeanStringObject<
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
    m_data: [116, 121, 112, 101, 78, 97, 109, 101, 115, 0],
};
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value: LeanStringObject<
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
    m_data: [101, 108, 105, 109, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminator___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCustomEliminator_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCustomEliminator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprCustomEliminator: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminator___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedCustomEliminators_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedCustomEliminators: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value) as *mut LeanObject;
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value) as *mut LeanObject;
pub static l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value) as *mut LeanObject] };
static mut l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value: LeanStringObject<
    4,
> = LeanStringObject {
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
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value: LeanCtorObject<
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
        l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [46, 116, 111, 83, 77, 97, 112, 0],
};
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value: LeanCtorObject<
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
        l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCustomEliminators___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCustomEliminators_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCustomEliminators___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprCustomEliminators: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCustomEliminators___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [99, 117, 115, 116, 111, 109, 69, 108, 105, 109, 105, 110, 97, 116, 111, 114, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,11023604290044921958 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_addCustomEliminatorEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 116, 97, 114, 103, 101, 116, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [69, 108, 105, 109, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,11863505845808076552 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9745472901445195361 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,10228487553473848708 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,834448862750540632 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,4199188339105210005 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,6816294245414320680 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,10884679213017361025 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value) as *mut LeanObject,18288507390640429121 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,643886601606611912 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,16036352676946811423 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,8020884807593767075 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [99, 117, 115, 116, 111, 109, 32, 96, 114, 101, 99, 96, 45, 108, 105, 107, 101, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 105, 110, 100, 117, 99, 116, 105, 111, 110, 96, 32, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value: LeanStringObject<849> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 849, m_capacity: 849, m_length: 792, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 99, 117, 115, 116, 111, 109, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 105, 110, 100, 117, 99, 116, 105, 111, 110, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 87, 104, 101, 110, 101, 118, 101, 114, 32, 116, 104, 101, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 105, 110, 32, 97, 110, 32, 96, 105, 110, 100, 117, 99, 116, 105, 111, 110, 96, 32, 99, 97, 108, 108, 32, 109, 97, 116, 99, 104, 101, 115, 32, 97, 32, 99, 117, 115, 116, 111, 109, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 44, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 100, 10, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 46, 32, 84, 104, 105, 115, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 114, 101, 100, 101, 102, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 116, 111, 32, 97, 32, 109, 111, 114, 101, 32, 117, 115, 101, 102, 117, 108, 10, 111, 110, 101, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 108, 101, 97, 110, 32, 101, 120, 97, 109, 112, 108, 101, 10, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 84, 104, 114, 101, 101, 32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 97, 108, 32, 58, 32, 70, 105, 110, 32, 51, 10, 10, 101, 120, 97, 109, 112, 108, 101, 32, 40, 120, 32, 58, 32, 84, 104, 114, 101, 101, 41, 32, 40, 112, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 80, 114, 111, 112, 41, 32, 58, 32, 112, 32, 120, 32, 58, 61, 32, 98, 121, 10, 32, 32, 105, 110, 100, 117, 99, 116, 105, 111, 110, 32, 120, 10, 32, 32, 45, 45, 32, 118, 97, 108, 32, 58, 32, 70, 105, 110, 32, 51, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 118, 97, 108, 226, 159, 169, 10, 10, 64, 91, 105, 110, 100, 117, 99, 116, 105, 111, 110, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 44, 32, 101, 108, 97, 98, 95, 97, 115, 95, 101, 108, 105, 109, 93, 10, 100, 101, 102, 32, 84, 104, 114, 101, 101, 46, 109, 121, 82, 101, 99, 32, 123, 109, 111, 116, 105, 118, 101, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 83, 111, 114, 116, 32, 117, 125, 10, 32, 32, 32, 32, 40, 122, 101, 114, 111, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 48, 226, 159, 169, 41, 32, 40, 111, 110, 101, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 49, 226, 159, 169, 41, 32, 40, 116, 119, 111, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 50, 226, 159, 169, 41, 32, 58, 10, 32, 32, 32, 32, 226, 136, 128, 32, 120, 44, 32, 109, 111, 116, 105, 118, 101, 32, 120, 10, 32, 32, 124, 32, 226, 159, 168, 48, 226, 159, 169, 32, 61, 62, 32, 122, 101, 114, 111, 32, 124, 32, 226, 159, 168, 49, 226, 159, 169, 32, 61, 62, 32, 111, 110, 101, 32, 124, 32, 226, 159, 168, 50, 226, 159, 169, 32, 61, 62, 32, 116, 119, 111, 10, 10, 101, 120, 97, 109, 112, 108, 101, 32, 40, 120, 32, 58, 32, 84, 104, 114, 101, 101, 41, 32, 40, 112, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 80, 114, 111, 112, 41, 32, 58, 32, 112, 32, 120, 32, 58, 61, 32, 98, 121, 10, 32, 32, 105, 110, 100, 117, 99, 116, 105, 111, 110, 32, 120, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 48, 226, 159, 169, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 49, 226, 159, 169, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 50, 226, 159, 169, 10, 96, 96, 96, 10, 10, 96, 64, 91, 99, 97, 115, 101, 115, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 93, 96, 32, 119, 111, 114, 107, 115, 32, 115, 105, 109, 105, 108, 97, 114, 108, 121, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,((( 913872705 as usize) << 1) | 1) as *mut LeanObject,14393908607051026736 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,186831489703476967 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value) as *mut LeanObject,2593740183373823535 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,11161229479889029418 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 97, 115, 101, 115, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,18063153688627580660 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [99, 117, 115, 116, 111, 109, 32, 96, 99, 97, 115, 101, 115, 79, 110, 96, 45, 108, 105, 107, 101, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 96, 32, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value: LeanStringObject<849> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 849, m_capacity: 849, m_length: 792, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 99, 117, 115, 116, 111, 109, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 87, 104, 101, 110, 101, 118, 101, 114, 32, 116, 104, 101, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 105, 110, 32, 97, 110, 32, 96, 99, 97, 115, 101, 115, 96, 32, 99, 97, 108, 108, 32, 109, 97, 116, 99, 104, 101, 115, 32, 97, 32, 99, 117, 115, 116, 111, 109, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 44, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 100, 10, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 79, 110, 96, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 46, 32, 84, 104, 105, 115, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 114, 101, 100, 101, 102, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 116, 111, 32, 97, 10, 109, 111, 114, 101, 32, 117, 115, 101, 102, 117, 108, 32, 111, 110, 101, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 108, 101, 97, 110, 32, 101, 120, 97, 109, 112, 108, 101, 10, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 84, 104, 114, 101, 101, 32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 97, 108, 32, 58, 32, 70, 105, 110, 32, 51, 10, 10, 101, 120, 97, 109, 112, 108, 101, 32, 40, 120, 32, 58, 32, 84, 104, 114, 101, 101, 41, 32, 40, 112, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 80, 114, 111, 112, 41, 32, 58, 32, 112, 32, 120, 32, 58, 61, 32, 98, 121, 10, 32, 32, 99, 97, 115, 101, 115, 32, 120, 10, 32, 32, 45, 45, 32, 118, 97, 108, 32, 58, 32, 70, 105, 110, 32, 51, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 118, 97, 108, 226, 159, 169, 10, 10, 64, 91, 99, 97, 115, 101, 115, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 44, 32, 101, 108, 97, 98, 95, 97, 115, 95, 101, 108, 105, 109, 93, 10, 100, 101, 102, 32, 84, 104, 114, 101, 101, 46, 109, 121, 82, 101, 99, 32, 123, 109, 111, 116, 105, 118, 101, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 83, 111, 114, 116, 32, 117, 125, 10, 32, 32, 32, 32, 40, 122, 101, 114, 111, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 48, 226, 159, 169, 41, 32, 40, 111, 110, 101, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 49, 226, 159, 169, 41, 32, 40, 116, 119, 111, 32, 58, 32, 109, 111, 116, 105, 118, 101, 32, 226, 159, 168, 50, 226, 159, 169, 41, 32, 58, 10, 32, 32, 32, 32, 226, 136, 128, 32, 120, 44, 32, 109, 111, 116, 105, 118, 101, 32, 120, 10, 32, 32, 124, 32, 226, 159, 168, 48, 226, 159, 169, 32, 61, 62, 32, 122, 101, 114, 111, 32, 124, 32, 226, 159, 168, 49, 226, 159, 169, 32, 61, 62, 32, 111, 110, 101, 32, 124, 32, 226, 159, 168, 50, 226, 159, 169, 32, 61, 62, 32, 116, 119, 111, 10, 10, 101, 120, 97, 109, 112, 108, 101, 32, 40, 120, 32, 58, 32, 84, 104, 114, 101, 101, 41, 32, 40, 112, 32, 58, 32, 84, 104, 114, 101, 101, 32, 226, 134, 146, 32, 80, 114, 111, 112, 41, 32, 58, 32, 112, 32, 120, 32, 58, 61, 32, 98, 121, 10, 32, 32, 99, 97, 115, 101, 115, 32, 120, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 48, 226, 159, 169, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 49, 226, 159, 169, 10, 32, 32, 45, 45, 32, 226, 138, 162, 32, 112, 32, 226, 159, 168, 50, 226, 159, 169, 10, 96, 96, 96, 10, 10, 96, 64, 91, 105, 110, 100, 117, 99, 116, 105, 111, 110, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 93, 96, 32, 119, 111, 114, 107, 115, 32, 115, 105, 109, 105, 108, 97, 114, 108, 121, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 105, 110, 100, 117, 99, 116, 105, 111, 110, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 0]};
static mut l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_getCustomEliminator_x3f___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_addImplicitTargets___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_getCustomEliminator_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getCustomEliminator_x3f___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(
    mut v_x_4533_: *mut LeanObject,
    mut v_x_4534_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4533_) == 0 {
        let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
        v___x_4535_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1;
        return v___x_4535_;
    } else {
        let mut v_val_4536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
        v_val_4536_ = lean_ctor_get(v_x_4533_, 0);
        lean_inc(v_val_4536_);
        lean_dec_ref_known(v_x_4533_, 1);
        v___x_4537_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3;
        v___x_4538_ = lean_unsigned_to_nat(1024);
        v___x_4539_ = l_Lean_Name_reprPrec(v_val_4536_, v___x_4538_);
        v___x_4540_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4540_, 0, v___x_4537_);
        lean_ctor_set(v___x_4540_, 1, v___x_4539_);
        v___x_4541_ = l_Repr_addAppParen(v___x_4540_, v_x_4534_);
        return v___x_4541_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___boxed(
    mut v_x_4542_: *mut LeanObject,
    mut v_x_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4544_: *mut LeanObject = core::ptr::null_mut();
    v_res_4544_ =
        l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(v_x_4542_, v_x_4543_);
    lean_dec(v_x_4543_);
    return v_res_4544_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_instReprElimAltInfo_repr_spec__1(
    mut v_a_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    v___x_4546_ = lean_nat_to_int(v_a_4545_);
    return v___x_4546_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    v___x_4560_ = lean_unsigned_to_nat(8);
    v___x_4561_ = lean_nat_to_int(v___x_4560_);
    return v___x_4561_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12() -> *mut LeanObject
{
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    v___x_4568_ = lean_unsigned_to_nat(13);
    v___x_4569_ = lean_nat_to_int(v___x_4568_);
    return v___x_4569_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17() -> *mut LeanObject
{
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    v___x_4576_ = lean_unsigned_to_nat(16);
    v___x_4577_ = lean_nat_to_int(v___x_4576_);
    return v___x_4577_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19() -> *mut LeanObject
{
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    v___x_4579_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0;
    v___x_4580_ = lean_string_length(v___x_4579_);
    return v___x_4580_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20() -> *mut LeanObject
{
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    v___x_4581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19,
    );
    v___x_4582_ = lean_nat_to_int(v___x_4581_);
    return v___x_4582_;
}
pub unsafe fn l_Lean_Meta_instReprElimAltInfo_repr___redArg(
    mut v_x_4587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_provesMotive_4591_: u8 = 0;
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    v_name_4588_ = lean_ctor_get(v_x_4587_, 0);
    lean_inc(v_name_4588_);
    v_declName_x3f_4589_ = lean_ctor_get(v_x_4587_, 1);
    lean_inc(v_declName_x3f_4589_);
    v_numFields_4590_ = lean_ctor_get(v_x_4587_, 2);
    lean_inc(v_numFields_4590_);
    v_provesMotive_4591_ = lean_ctor_get_uint8(
        v_x_4587_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_x_4587_);
    v___x_4592_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5;
    v___x_4593_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6;
    v___x_4594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7,
    );
    v___x_4595_ = lean_unsigned_to_nat(0);
    v___x_4596_ = l_Lean_Name_reprPrec(v_name_4588_, v___x_4595_);
    v___x_4597_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4597_, 0, v___x_4594_);
    lean_ctor_set(v___x_4597_, 1, v___x_4596_);
    v___x_4598_ = 0;
    v___x_4599_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4599_, 0, v___x_4597_);
    lean_ctor_set_uint8(
        v___x_4599_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4598_,
    );
    v___x_4600_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4600_, 0, v___x_4593_);
    lean_ctor_set(v___x_4600_, 1, v___x_4599_);
    v___x_4601_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9;
    v___x_4602_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4602_, 0, v___x_4600_);
    lean_ctor_set(v___x_4602_, 1, v___x_4601_);
    v___x_4603_ = lean_box(1);
    v___x_4604_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4604_, 0, v___x_4602_);
    lean_ctor_set(v___x_4604_, 1, v___x_4603_);
    v___x_4605_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11;
    v___x_4606_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4606_, 0, v___x_4604_);
    lean_ctor_set(v___x_4606_, 1, v___x_4605_);
    v___x_4607_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4607_, 0, v___x_4606_);
    lean_ctor_set(v___x_4607_, 1, v___x_4592_);
    v___x_4608_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12,
    );
    v___x_4609_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(
        v_declName_x3f_4589_,
        v___x_4595_,
    );
    v___x_4610_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4610_, 0, v___x_4608_);
    lean_ctor_set(v___x_4610_, 1, v___x_4609_);
    v___x_4611_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4611_, 0, v___x_4610_);
    lean_ctor_set_uint8(
        v___x_4611_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4598_,
    );
    v___x_4612_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4612_, 0, v___x_4607_);
    lean_ctor_set(v___x_4612_, 1, v___x_4611_);
    v___x_4613_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4613_, 0, v___x_4612_);
    lean_ctor_set(v___x_4613_, 1, v___x_4601_);
    v___x_4614_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4614_, 0, v___x_4613_);
    lean_ctor_set(v___x_4614_, 1, v___x_4603_);
    v___x_4615_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14;
    v___x_4616_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4616_, 0, v___x_4614_);
    lean_ctor_set(v___x_4616_, 1, v___x_4615_);
    v___x_4617_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4617_, 0, v___x_4616_);
    lean_ctor_set(v___x_4617_, 1, v___x_4592_);
    v___x_4618_ = l_Nat_reprFast(v_numFields_4590_);
    v___x_4619_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4619_, 0, v___x_4618_);
    v___x_4620_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4620_, 0, v___x_4608_);
    lean_ctor_set(v___x_4620_, 1, v___x_4619_);
    v___x_4621_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4621_, 0, v___x_4620_);
    lean_ctor_set_uint8(
        v___x_4621_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4598_,
    );
    v___x_4622_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4622_, 0, v___x_4617_);
    lean_ctor_set(v___x_4622_, 1, v___x_4621_);
    v___x_4623_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4623_, 0, v___x_4622_);
    lean_ctor_set(v___x_4623_, 1, v___x_4601_);
    v___x_4624_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4624_, 0, v___x_4623_);
    lean_ctor_set(v___x_4624_, 1, v___x_4603_);
    v___x_4625_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16;
    v___x_4626_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4626_, 0, v___x_4624_);
    lean_ctor_set(v___x_4626_, 1, v___x_4625_);
    v___x_4627_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4627_, 0, v___x_4626_);
    lean_ctor_set(v___x_4627_, 1, v___x_4592_);
    v___x_4628_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17,
    );
    v___x_4629_ = l_Bool_repr___redArg(v_provesMotive_4591_);
    v___x_4630_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4630_, 0, v___x_4628_);
    lean_ctor_set(v___x_4630_, 1, v___x_4629_);
    v___x_4631_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4631_, 0, v___x_4630_);
    lean_ctor_set_uint8(
        v___x_4631_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4598_,
    );
    v___x_4632_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4632_, 0, v___x_4627_);
    lean_ctor_set(v___x_4632_, 1, v___x_4631_);
    v___x_4633_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20,
    );
    v___x_4634_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21;
    v___x_4635_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4635_, 0, v___x_4634_);
    lean_ctor_set(v___x_4635_, 1, v___x_4632_);
    v___x_4636_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22;
    v___x_4637_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4637_, 0, v___x_4635_);
    lean_ctor_set(v___x_4637_, 1, v___x_4636_);
    v___x_4638_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4638_, 0, v___x_4633_);
    lean_ctor_set(v___x_4638_, 1, v___x_4637_);
    v___x_4639_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    lean_ctor_set_uint8(
        v___x_4639_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4598_,
    );
    return v___x_4639_;
}
pub unsafe fn l_Lean_Meta_instReprElimAltInfo_repr(
    mut v_x_4640_: *mut LeanObject,
    mut v_prec_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    v___x_4642_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_x_4640_);
    return v___x_4642_;
}
pub unsafe fn l_Lean_Meta_instReprElimAltInfo_repr___boxed(
    mut v_x_4643_: *mut LeanObject,
    mut v_prec_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4645_: *mut LeanObject = core::ptr::null_mut();
    v_res_4645_ = l_Lean_Meta_instReprElimAltInfo_repr(v_x_4643_, v_prec_4644_);
    lean_dec(v_prec_4644_);
    return v_res_4645_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(
    mut v_x_4655_: *mut LeanObject,
    mut v_x_4656_: *mut LeanObject,
    mut v_x_4657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4662_: u8 = 0;
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4657_) == 0 {
                    lean_dec(v_x_4655_);
                    return v_x_4656_;
                } else {
                    v_head_4658_ = lean_ctor_get(v_x_4657_, 0);
                    v_tail_4659_ = lean_ctor_get(v_x_4657_, 1);
                    v_isSharedCheck_4670_ = (!lean_is_exclusive(v_x_4657_)) as u8;
                    if v_isSharedCheck_4670_ == 0 {
                        v___x_4661_ = v_x_4657_;
                        v_isShared_4662_ = v_isSharedCheck_4670_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4659_);
                        lean_inc(v_head_4658_);
                        lean_dec(v_x_4657_);
                        v___x_4661_ = lean_box(0);
                        v_isShared_4662_ = v_isSharedCheck_4670_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4655_);
                if v_isShared_4662_ == 0 {
                    lean_ctor_set_tag(v___x_4661_, 5);
                    lean_ctor_set(v___x_4661_, 1, v_x_4655_);
                    lean_ctor_set(v___x_4661_, 0, v_x_4656_);
                    v___x_4664_ = v___x_4661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_x_4656_);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 1, v_x_4655_);
                    v___x_4664_ = v_reuseFailAlloc_4669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4665_ = l_Nat_reprFast(v_head_4658_);
                v___x_4666_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4666_, 0, v___x_4665_);
                v___x_4667_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4667_, 0, v___x_4664_);
                lean_ctor_set(v___x_4667_, 1, v___x_4666_);
                v_x_4656_ = v___x_4667_;
                v_x_4657_ = v_tail_4659_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(
    mut v_x_4671_: *mut LeanObject,
    mut v_x_4672_: *mut LeanObject,
    mut v_x_4673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4673_) == 0 {
                    lean_dec(v_x_4671_);
                    return v_x_4672_;
                } else {
                    v_head_4674_ = lean_ctor_get(v_x_4673_, 0);
                    v_tail_4675_ = lean_ctor_get(v_x_4673_, 1);
                    v_isSharedCheck_4686_ = (!lean_is_exclusive(v_x_4673_)) as u8;
                    if v_isSharedCheck_4686_ == 0 {
                        v___x_4677_ = v_x_4673_;
                        v_isShared_4678_ = v_isSharedCheck_4686_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4675_);
                        lean_inc(v_head_4674_);
                        lean_dec(v_x_4673_);
                        v___x_4677_ = lean_box(0);
                        v_isShared_4678_ = v_isSharedCheck_4686_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4671_);
                if v_isShared_4678_ == 0 {
                    lean_ctor_set_tag(v___x_4677_, 5);
                    lean_ctor_set(v___x_4677_, 1, v_x_4671_);
                    lean_ctor_set(v___x_4677_, 0, v_x_4672_);
                    v___x_4680_ = v___x_4677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_x_4672_);
                    lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_x_4671_);
                    v___x_4680_ = v_reuseFailAlloc_4685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4681_ = l_Nat_reprFast(v_head_4674_);
                v___x_4682_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4682_, 0, v___x_4681_);
                v___x_4683_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4683_, 0, v___x_4680_);
                lean_ctor_set(v___x_4683_, 1, v___x_4682_);
                v___x_4684_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(v_x_4671_, v___x_4683_, v_tail_4675_);
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Nat_reprFast(v___y_4687_);
    v___x_4689_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4689_, 0, v___x_4688_);
    return v___x_4689_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(
    mut v_x_4690_: *mut LeanObject,
    mut v_x_4691_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4690_) == 0 {
        let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4691_);
        v___x_4692_ = lean_box(0);
        return v___x_4692_;
    } else {
        let mut v_tail_4693_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4693_ = lean_ctor_get(v_x_4690_, 1);
        if lean_obj_tag(v_tail_4693_) == 0 {
            let mut v_head_4694_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_4691_);
            v_head_4694_ = lean_ctor_get(v_x_4690_, 0);
            lean_inc(v_head_4694_);
            lean_dec_ref_known(v_x_4690_, 2);
            v___x_4695_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_4694_);
            return v___x_4695_;
        } else {
            let mut v_head_4696_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4693_);
            v_head_4696_ = lean_ctor_get(v_x_4690_, 0);
            lean_inc(v_head_4696_);
            lean_dec_ref_known(v_x_4690_, 2);
            v___x_4697_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_4696_);
            v___x_4698_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(v_x_4691_, v___x_4697_, v_tail_4693_);
            return v___x_4698_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4704_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0;
    v___x_4705_ = lean_string_length(v___x_4704_);
    return v___x_4705_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    v___x_4706_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3,
    );
    v___x_4707_ = lean_nat_to_int(v___x_4706_);
    return v___x_4707_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(
    mut v_xs_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: u8 = 0;
    v___x_4716_ = lean_array_get_size(v_xs_4715_);
    v___x_4717_ = lean_unsigned_to_nat(0);
    v___x_4718_ = lean_nat_dec_eq(v___x_4716_, v___x_4717_);
    if v___x_4718_ == 0 {
        let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
        v___x_4719_ = lean_array_to_list(v_xs_4715_);
        v___x_4720_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
        v___x_4721_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(v___x_4719_, v___x_4720_);
        v___x_4722_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4,
        );
        v___x_4723_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5;
        v___x_4724_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4724_, 0, v___x_4723_);
        lean_ctor_set(v___x_4724_, 1, v___x_4721_);
        v___x_4725_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6;
        v___x_4726_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4726_, 0, v___x_4724_);
        lean_ctor_set(v___x_4726_, 1, v___x_4725_);
        v___x_4727_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_4727_, 0, v___x_4722_);
        lean_ctor_set(v___x_4727_, 1, v___x_4726_);
        v___x_4728_ = l_Std_Format_fill(v___x_4727_);
        return v___x_4728_;
    } else {
        let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4715_);
        v___x_4729_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8;
        return v___x_4729_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(
    mut v_x_4730_: *mut LeanObject,
    mut v_x_4731_: *mut LeanObject,
    mut v_x_4732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4737_: u8 = 0;
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4732_) == 0 {
                    lean_dec(v_x_4730_);
                    return v_x_4731_;
                } else {
                    v_head_4733_ = lean_ctor_get(v_x_4732_, 0);
                    v_tail_4734_ = lean_ctor_get(v_x_4732_, 1);
                    v_isSharedCheck_4744_ = (!lean_is_exclusive(v_x_4732_)) as u8;
                    if v_isSharedCheck_4744_ == 0 {
                        v___x_4736_ = v_x_4732_;
                        v_isShared_4737_ = v_isSharedCheck_4744_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4734_);
                        lean_inc(v_head_4733_);
                        lean_dec(v_x_4732_);
                        v___x_4736_ = lean_box(0);
                        v_isShared_4737_ = v_isSharedCheck_4744_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4730_);
                if v_isShared_4737_ == 0 {
                    lean_ctor_set_tag(v___x_4736_, 5);
                    lean_ctor_set(v___x_4736_, 1, v_x_4730_);
                    lean_ctor_set(v___x_4736_, 0, v_x_4731_);
                    v___x_4739_ = v___x_4736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4743_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_x_4731_);
                    lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_x_4730_);
                    v___x_4739_ = v_reuseFailAlloc_4743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4740_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_4733_);
                v___x_4741_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4741_, 0, v___x_4739_);
                lean_ctor_set(v___x_4741_, 1, v___x_4740_);
                v_x_4731_ = v___x_4741_;
                v_x_4732_ = v_tail_4734_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(
    mut v_x_4745_: *mut LeanObject,
    mut v_x_4746_: *mut LeanObject,
    mut v_x_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4747_) == 0 {
                    lean_dec(v_x_4745_);
                    return v_x_4746_;
                } else {
                    v_head_4748_ = lean_ctor_get(v_x_4747_, 0);
                    v_tail_4749_ = lean_ctor_get(v_x_4747_, 1);
                    v_isSharedCheck_4759_ = (!lean_is_exclusive(v_x_4747_)) as u8;
                    if v_isSharedCheck_4759_ == 0 {
                        v___x_4751_ = v_x_4747_;
                        v_isShared_4752_ = v_isSharedCheck_4759_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4749_);
                        lean_inc(v_head_4748_);
                        lean_dec(v_x_4747_);
                        v___x_4751_ = lean_box(0);
                        v_isShared_4752_ = v_isSharedCheck_4759_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4745_);
                if v_isShared_4752_ == 0 {
                    lean_ctor_set_tag(v___x_4751_, 5);
                    lean_ctor_set(v___x_4751_, 1, v_x_4745_);
                    lean_ctor_set(v___x_4751_, 0, v_x_4746_);
                    v___x_4754_ = v___x_4751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_x_4746_);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_x_4745_);
                    v___x_4754_ = v_reuseFailAlloc_4758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4755_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_4748_);
                v___x_4756_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4756_, 0, v___x_4754_);
                lean_ctor_set(v___x_4756_, 1, v___x_4755_);
                v___x_4757_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(v_x_4745_, v___x_4756_, v_tail_4749_);
                return v___x_4757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(
    mut v_x_4760_: *mut LeanObject,
    mut v_x_4761_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4760_) == 0 {
        let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4761_);
        v___x_4762_ = lean_box(0);
        return v___x_4762_;
    } else {
        let mut v_tail_4763_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4763_ = lean_ctor_get(v_x_4760_, 1);
        if lean_obj_tag(v_tail_4763_) == 0 {
            let mut v_head_4764_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_4761_);
            v_head_4764_ = lean_ctor_get(v_x_4760_, 0);
            lean_inc(v_head_4764_);
            lean_dec_ref_known(v_x_4760_, 2);
            v___x_4765_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_4764_);
            return v___x_4765_;
        } else {
            let mut v_head_4766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4763_);
            v_head_4766_ = lean_ctor_get(v_x_4760_, 0);
            lean_inc(v_head_4766_);
            lean_dec_ref_known(v_x_4760_, 2);
            v___x_4767_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_4766_);
            v___x_4768_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(v_x_4761_, v___x_4767_, v_tail_4763_);
            return v___x_4768_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(
    mut v_xs_4769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u8 = 0;
    v___x_4770_ = lean_array_get_size(v_xs_4769_);
    v___x_4771_ = lean_unsigned_to_nat(0);
    v___x_4772_ = lean_nat_dec_eq(v___x_4770_, v___x_4771_);
    if v___x_4772_ == 0 {
        let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
        v___x_4773_ = lean_array_to_list(v_xs_4769_);
        v___x_4774_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
        v___x_4775_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(v___x_4773_, v___x_4774_);
        v___x_4776_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4,
        );
        v___x_4777_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5;
        v___x_4778_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4778_, 0, v___x_4777_);
        lean_ctor_set(v___x_4778_, 1, v___x_4775_);
        v___x_4779_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6;
        v___x_4780_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4780_, 0, v___x_4778_);
        lean_ctor_set(v___x_4780_, 1, v___x_4779_);
        v___x_4781_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_4781_, 0, v___x_4776_);
        lean_ctor_set(v___x_4781_, 1, v___x_4780_);
        v___x_4782_ = l_Std_Format_fill(v___x_4781_);
        return v___x_4782_;
    } else {
        let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4769_);
        v___x_4783_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8;
        return v___x_4783_;
    }
}
pub unsafe fn _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    v___x_4793_ = lean_unsigned_to_nat(12);
    v___x_4794_ = lean_nat_to_int(v___x_4793_);
    return v___x_4794_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    v___x_4804_ = lean_unsigned_to_nat(14);
    v___x_4805_ = lean_nat_to_int(v___x_4804_);
    return v___x_4805_;
}
pub unsafe fn _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    v___x_4812_ = lean_unsigned_to_nat(24);
    v___x_4813_ = lean_nat_to_int(v___x_4812_);
    return v___x_4813_;
}
pub unsafe fn l_Lean_Meta_instReprElimInfo_repr___redArg(
    mut v_x_4814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimExpr_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimType_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motivePos_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetsPos_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_altsInfo_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numComplexMotiveArgs_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: u8 = 0;
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    v_elimExpr_4815_ = lean_ctor_get(v_x_4814_, 0);
    lean_inc_ref(v_elimExpr_4815_);
    v_elimType_4816_ = lean_ctor_get(v_x_4814_, 1);
    lean_inc_ref(v_elimType_4816_);
    v_motivePos_4817_ = lean_ctor_get(v_x_4814_, 2);
    lean_inc(v_motivePos_4817_);
    v_targetsPos_4818_ = lean_ctor_get(v_x_4814_, 3);
    lean_inc_ref(v_targetsPos_4818_);
    v_altsInfo_4819_ = lean_ctor_get(v_x_4814_, 4);
    lean_inc_ref(v_altsInfo_4819_);
    v_numComplexMotiveArgs_4820_ = lean_ctor_get(v_x_4814_, 5);
    lean_inc(v_numComplexMotiveArgs_4820_);
    lean_dec_ref(v_x_4814_);
    v___x_4821_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5;
    v___x_4822_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3;
    v___x_4823_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once),
        _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4,
    );
    v___x_4824_ = lean_unsigned_to_nat(0);
    v___x_4825_ = l_Lean_instReprExpr_repr(v_elimExpr_4815_, v___x_4824_);
    v___x_4826_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4826_, 0, v___x_4823_);
    lean_ctor_set(v___x_4826_, 1, v___x_4825_);
    v___x_4827_ = 0;
    v___x_4828_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4828_, 0, v___x_4826_);
    lean_ctor_set_uint8(
        v___x_4828_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4829_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4829_, 0, v___x_4822_);
    lean_ctor_set(v___x_4829_, 1, v___x_4828_);
    v___x_4830_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9;
    v___x_4831_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4831_, 0, v___x_4829_);
    lean_ctor_set(v___x_4831_, 1, v___x_4830_);
    v___x_4832_ = lean_box(1);
    v___x_4833_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4833_, 0, v___x_4831_);
    lean_ctor_set(v___x_4833_, 1, v___x_4832_);
    v___x_4834_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6;
    v___x_4835_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4835_, 0, v___x_4833_);
    lean_ctor_set(v___x_4835_, 1, v___x_4834_);
    v___x_4836_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4836_, 0, v___x_4835_);
    lean_ctor_set(v___x_4836_, 1, v___x_4821_);
    v___x_4837_ = l_Lean_instReprExpr_repr(v_elimType_4816_, v___x_4824_);
    v___x_4838_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4838_, 0, v___x_4823_);
    lean_ctor_set(v___x_4838_, 1, v___x_4837_);
    v___x_4839_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4839_, 0, v___x_4838_);
    lean_ctor_set_uint8(
        v___x_4839_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4840_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4840_, 0, v___x_4836_);
    lean_ctor_set(v___x_4840_, 1, v___x_4839_);
    v___x_4841_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4841_, 0, v___x_4840_);
    lean_ctor_set(v___x_4841_, 1, v___x_4830_);
    v___x_4842_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4842_, 0, v___x_4841_);
    lean_ctor_set(v___x_4842_, 1, v___x_4832_);
    v___x_4843_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8;
    v___x_4844_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4844_, 0, v___x_4842_);
    lean_ctor_set(v___x_4844_, 1, v___x_4843_);
    v___x_4845_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4845_, 0, v___x_4844_);
    lean_ctor_set(v___x_4845_, 1, v___x_4821_);
    v___x_4846_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12,
    );
    v___x_4847_ = l_Nat_reprFast(v_motivePos_4817_);
    v___x_4848_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4848_, 0, v___x_4847_);
    v___x_4849_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4849_, 0, v___x_4846_);
    lean_ctor_set(v___x_4849_, 1, v___x_4848_);
    v___x_4850_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4850_, 0, v___x_4849_);
    lean_ctor_set_uint8(
        v___x_4850_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4851_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4851_, 0, v___x_4845_);
    lean_ctor_set(v___x_4851_, 1, v___x_4850_);
    v___x_4852_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4852_, 0, v___x_4851_);
    lean_ctor_set(v___x_4852_, 1, v___x_4830_);
    v___x_4853_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4853_, 0, v___x_4852_);
    lean_ctor_set(v___x_4853_, 1, v___x_4832_);
    v___x_4854_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10;
    v___x_4855_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4855_, 0, v___x_4853_);
    lean_ctor_set(v___x_4855_, 1, v___x_4854_);
    v___x_4856_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4856_, 0, v___x_4855_);
    lean_ctor_set(v___x_4856_, 1, v___x_4821_);
    v___x_4857_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once),
        _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11,
    );
    v___x_4858_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(v_targetsPos_4818_);
    v___x_4859_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4859_, 0, v___x_4857_);
    lean_ctor_set(v___x_4859_, 1, v___x_4858_);
    v___x_4860_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4860_, 0, v___x_4859_);
    lean_ctor_set_uint8(
        v___x_4860_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4861_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4861_, 0, v___x_4856_);
    lean_ctor_set(v___x_4861_, 1, v___x_4860_);
    v___x_4862_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4862_, 0, v___x_4861_);
    lean_ctor_set(v___x_4862_, 1, v___x_4830_);
    v___x_4863_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4863_, 0, v___x_4862_);
    lean_ctor_set(v___x_4863_, 1, v___x_4832_);
    v___x_4864_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13;
    v___x_4865_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4865_, 0, v___x_4863_);
    lean_ctor_set(v___x_4865_, 1, v___x_4864_);
    v___x_4866_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4866_, 0, v___x_4865_);
    lean_ctor_set(v___x_4866_, 1, v___x_4821_);
    v___x_4867_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(v_altsInfo_4819_);
    v___x_4868_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4868_, 0, v___x_4823_);
    lean_ctor_set(v___x_4868_, 1, v___x_4867_);
    v___x_4869_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4869_, 0, v___x_4868_);
    lean_ctor_set_uint8(
        v___x_4869_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4870_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4870_, 0, v___x_4866_);
    lean_ctor_set(v___x_4870_, 1, v___x_4869_);
    v___x_4871_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4871_, 0, v___x_4870_);
    lean_ctor_set(v___x_4871_, 1, v___x_4830_);
    v___x_4872_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4872_, 0, v___x_4871_);
    lean_ctor_set(v___x_4872_, 1, v___x_4832_);
    v___x_4873_ = l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15;
    v___x_4874_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4874_, 0, v___x_4872_);
    lean_ctor_set(v___x_4874_, 1, v___x_4873_);
    v___x_4875_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4875_, 0, v___x_4874_);
    lean_ctor_set(v___x_4875_, 1, v___x_4821_);
    v___x_4876_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16,
    );
    v___x_4877_ = l_Nat_reprFast(v_numComplexMotiveArgs_4820_);
    v___x_4878_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4878_, 0, v___x_4877_);
    v___x_4879_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4879_, 0, v___x_4876_);
    lean_ctor_set(v___x_4879_, 1, v___x_4878_);
    v___x_4880_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4880_, 0, v___x_4879_);
    lean_ctor_set_uint8(
        v___x_4880_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    v___x_4881_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4881_, 0, v___x_4875_);
    lean_ctor_set(v___x_4881_, 1, v___x_4880_);
    v___x_4882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20,
    );
    v___x_4883_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21;
    v___x_4884_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    lean_ctor_set(v___x_4884_, 1, v___x_4881_);
    v___x_4885_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22;
    v___x_4886_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4886_, 0, v___x_4884_);
    lean_ctor_set(v___x_4886_, 1, v___x_4885_);
    v___x_4887_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4887_, 0, v___x_4882_);
    lean_ctor_set(v___x_4887_, 1, v___x_4886_);
    v___x_4888_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4888_, 0, v___x_4887_);
    lean_ctor_set_uint8(
        v___x_4888_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4827_,
    );
    return v___x_4888_;
}
pub unsafe fn l_Lean_Meta_instReprElimInfo_repr(
    mut v_x_4889_: *mut LeanObject,
    mut v_prec_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Lean_Meta_instReprElimInfo_repr___redArg(v_x_4889_);
    return v___x_4891_;
}
pub unsafe fn l_Lean_Meta_instReprElimInfo_repr___boxed(
    mut v_x_4892_: *mut LeanObject,
    mut v_prec_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4894_: *mut LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Lean_Meta_instReprElimInfo_repr(v_x_4892_, v_prec_4893_);
    lean_dec(v_prec_4893_);
    return v_res_4894_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2() -> *mut LeanObject {
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    v___x_4900_ = lean_box(0);
    v___x_4901_ = l_Lean_Meta_instInhabitedElimInfo_default___closed__1;
    v___x_4902_ = l_Lean_Expr_const___override(v___x_4901_, v___x_4900_);
    return v___x_4902_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4() -> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_Lean_Meta_instInhabitedElimInfo_default___closed__3;
    v___x_4906_ = lean_unsigned_to_nat(0);
    v___x_4907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedElimInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once),
        _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2,
    );
    v___x_4908_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4908_, 0, v___x_4907_);
    lean_ctor_set(v___x_4908_, 1, v___x_4907_);
    lean_ctor_set(v___x_4908_, 2, v___x_4906_);
    lean_ctor_set(v___x_4908_, 3, v___x_4905_);
    lean_ctor_set(v___x_4908_, 4, v___x_4905_);
    lean_ctor_set(v___x_4908_, 5, v___x_4906_);
    return v___x_4908_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedElimInfo_default() -> *mut LeanObject {
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    v___x_4909_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedElimInfo_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once),
        _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4,
    );
    return v___x_4909_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedElimInfo() -> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    v___x_4910_ = l_Lean_Meta_instInhabitedElimInfo_default;
    return v___x_4910_;
}
pub unsafe fn l_Lean_Meta_altArity(
    mut v_motive_4911_: *mut LeanObject,
    mut v_n_4912_: *mut LeanObject,
    mut v_x_4913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_body_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: u8 = 0;
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4913_) {
                7 => {
                    v_body_4914_ = lean_ctor_get(v_x_4913_, 2);
                    v___x_4915_ = lean_unsigned_to_nat(1);
                    v___x_4916_ = lean_nat_add(v_n_4912_, v___x_4915_);
                    lean_dec(v_n_4912_);
                    v_n_4912_ = v___x_4916_;
                    v_x_4913_ = v_body_4914_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_4918_ = lean_ctor_get(v_x_4913_, 3);
                    v___x_4919_ = lean_unsigned_to_nat(1);
                    v___x_4920_ = lean_nat_add(v_n_4912_, v___x_4919_);
                    lean_dec(v_n_4912_);
                    v_n_4912_ = v___x_4920_;
                    v_x_4913_ = v_body_4918_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_4922_ = l_Lean_Expr_getAppFn(v_x_4913_);
                    v___x_4923_ = lean_expr_eqv(v___x_4922_, v_motive_4911_);
                    lean_dec_ref(v___x_4922_);
                    v___x_4924_ = lean_box((v___x_4923_) as usize);
                    v___x_4925_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4925_, 0, v_n_4912_);
                    lean_ctor_set(v___x_4925_, 1, v___x_4924_);
                    return v___x_4925_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_altArity___boxed(
    mut v_motive_4926_: *mut LeanObject,
    mut v_n_4927_: *mut LeanObject,
    mut v_x_4928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4929_: *mut LeanObject = core::ptr::null_mut();
    v_res_4929_ = l_Lean_Meta_altArity(v_motive_4926_, v_n_4927_, v_x_4928_);
    lean_dec_ref(v_x_4928_);
    lean_dec_ref(v_motive_4926_);
    return v_res_4929_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(
    mut v_k_4930_: *mut LeanObject,
    mut v_b_4931_: *mut LeanObject,
    mut v_c_4932_: *mut LeanObject,
    mut v___y_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4936_);
    lean_inc_ref(v___y_4935_);
    lean_inc(v___y_4934_);
    lean_inc_ref(v___y_4933_);
    v___x_4938_ = lean_apply_7(
        v_k_4930_,
        v_b_4931_,
        v_c_4932_,
        v___y_4933_,
        v___y_4934_,
        v___y_4935_,
        v___y_4936_,
        lean_box(0),
    );
    return v___x_4938_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed(
    mut v_k_4939_: *mut LeanObject,
    mut v_b_4940_: *mut LeanObject,
    mut v_c_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
    mut v___y_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4947_: *mut LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(v_k_4939_, v_b_4940_, v_c_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
    lean_dec(v___y_4945_);
    lean_dec_ref(v___y_4944_);
    lean_dec(v___y_4943_);
    lean_dec_ref(v___y_4942_);
    return v_res_4947_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(
    mut v_type_4948_: *mut LeanObject,
    mut v_k_4949_: *mut LeanObject,
    mut v_cleanupAnnotations_4950_: u8,
    mut v_whnfType_4951_: u8,
    mut v___y_4952_: *mut LeanObject,
    mut v___y_4953_: *mut LeanObject,
    mut v___y_4954_: *mut LeanObject,
    mut v___y_4955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_a_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4970_: u8 = 0;
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4957_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4957_, 0, v_k_4949_);
                v___x_4958_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_4948_,
                    v___f_4957_,
                    v_cleanupAnnotations_4950_,
                    v_whnfType_4951_,
                    v___y_4952_,
                    v___y_4953_,
                    v___y_4954_,
                    v___y_4955_,
                );
                if lean_obj_tag(v___x_4958_) == 0 {
                    v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
                    v_isSharedCheck_4966_ = (!lean_is_exclusive(v___x_4958_)) as u8;
                    if v_isSharedCheck_4966_ == 0 {
                        v___x_4961_ = v___x_4958_;
                        v_isShared_4962_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4959_);
                        lean_dec(v___x_4958_);
                        v___x_4961_ = lean_box(0);
                        v_isShared_4962_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4967_ = lean_ctor_get(v___x_4958_, 0);
                    v_isSharedCheck_4974_ = (!lean_is_exclusive(v___x_4958_)) as u8;
                    if v_isSharedCheck_4974_ == 0 {
                        v___x_4969_ = v___x_4958_;
                        v_isShared_4970_ = v_isSharedCheck_4974_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4967_);
                        lean_dec(v___x_4958_);
                        v___x_4969_ = lean_box(0);
                        v_isShared_4970_ = v_isSharedCheck_4974_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4962_ == 0 {
                    v___x_4964_ = v___x_4961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
                    v___x_4964_ = v_reuseFailAlloc_4965_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4964_;
            }
            3 => {
                if v_isShared_4970_ == 0 {
                    v___x_4972_ = v___x_4969_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
                    v___x_4972_ = v_reuseFailAlloc_4973_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___boxed(
    mut v_type_4975_: *mut LeanObject,
    mut v_k_4976_: *mut LeanObject,
    mut v_cleanupAnnotations_4977_: *mut LeanObject,
    mut v_whnfType_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
    mut v___y_4982_: *mut LeanObject,
    mut v___y_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4984_: u8 = 0;
    let mut v_whnfType_boxed_4985_: u8 = 0;
    let mut v_res_4986_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4984_ = (lean_unbox(v_cleanupAnnotations_4977_) as u8);
    v_whnfType_boxed_4985_ = (lean_unbox(v_whnfType_4978_) as u8);
    v_res_4986_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(
            v_type_4975_,
            v_k_4976_,
            v_cleanupAnnotations_boxed_4984_,
            v_whnfType_boxed_4985_,
            v___y_4979_,
            v___y_4980_,
            v___y_4981_,
            v___y_4982_,
        );
    lean_dec(v___y_4982_);
    lean_dec_ref(v___y_4981_);
    lean_dec(v___y_4980_);
    lean_dec_ref(v___y_4979_);
    return v_res_4986_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(
    mut v_00_u03b1_4987_: *mut LeanObject,
    mut v_type_4988_: *mut LeanObject,
    mut v_k_4989_: *mut LeanObject,
    mut v_cleanupAnnotations_4990_: u8,
    mut v_whnfType_4991_: u8,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    v___x_4997_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(
            v_type_4988_,
            v_k_4989_,
            v_cleanupAnnotations_4990_,
            v_whnfType_4991_,
            v___y_4992_,
            v___y_4993_,
            v___y_4994_,
            v___y_4995_,
        );
    return v___x_4997_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___boxed(
    mut v_00_u03b1_4998_: *mut LeanObject,
    mut v_type_4999_: *mut LeanObject,
    mut v_k_5000_: *mut LeanObject,
    mut v_cleanupAnnotations_5001_: *mut LeanObject,
    mut v_whnfType_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
    mut v___y_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5008_: u8 = 0;
    let mut v_whnfType_boxed_5009_: u8 = 0;
    let mut v_res_5010_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5008_ = (lean_unbox(v_cleanupAnnotations_5001_) as u8);
    v_whnfType_boxed_5009_ = (lean_unbox(v_whnfType_5002_) as u8);
    v_res_5010_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(
        v_00_u03b1_4998_,
        v_type_4999_,
        v_k_5000_,
        v_cleanupAnnotations_boxed_5008_,
        v_whnfType_boxed_5009_,
        v___y_5003_,
        v___y_5004_,
        v___y_5005_,
        v___y_5006_,
    );
    lean_dec(v___y_5006_);
    lean_dec_ref(v___y_5005_);
    lean_dec(v___y_5004_);
    lean_dec_ref(v___y_5003_);
    return v_res_5010_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(
    mut v_msgData_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    v___x_5017_ = lean_st_ref_get(v___y_5015_);
    v_env_5018_ = lean_ctor_get(v___x_5017_, 0);
    lean_inc_ref(v_env_5018_);
    lean_dec(v___x_5017_);
    v___x_5019_ = lean_st_ref_get(v___y_5013_);
    v_mctx_5020_ = lean_ctor_get(v___x_5019_, 0);
    lean_inc_ref(v_mctx_5020_);
    lean_dec(v___x_5019_);
    v_lctx_5021_ = lean_ctor_get(v___y_5012_, 2);
    v_options_5022_ = lean_ctor_get(v___y_5014_, 2);
    lean_inc_ref(v_options_5022_);
    lean_inc_ref(v_lctx_5021_);
    v___x_5023_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5023_, 0, v_env_5018_);
    lean_ctor_set(v___x_5023_, 1, v_mctx_5020_);
    lean_ctor_set(v___x_5023_, 2, v_lctx_5021_);
    lean_ctor_set(v___x_5023_, 3, v_options_5022_);
    v___x_5024_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5024_, 0, v___x_5023_);
    lean_ctor_set(v___x_5024_, 1, v_msgData_5011_);
    v___x_5025_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5025_, 0, v___x_5024_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(
    mut v_msgData_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5032_: *mut LeanObject = core::ptr::null_mut();
    v_res_5032_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msgData_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
    lean_dec(v___y_5030_);
    lean_dec_ref(v___y_5029_);
    lean_dec(v___y_5028_);
    lean_dec_ref(v___y_5027_);
    return v_res_5032_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
    mut v_msg_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5039_ = lean_ctor_get(v___y_5036_, 5);
                v___x_5040_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
                v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
                v_isSharedCheck_5049_ = (!lean_is_exclusive(v___x_5040_)) as u8;
                if v_isSharedCheck_5049_ == 0 {
                    v___x_5043_ = v___x_5040_;
                    v_isShared_5044_ = v_isSharedCheck_5049_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5041_);
                    lean_dec(v___x_5040_);
                    v___x_5043_ = lean_box(0);
                    v_isShared_5044_ = v_isSharedCheck_5049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5039_);
                v___x_5045_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5045_, 0, v_ref_5039_);
                lean_ctor_set(v___x_5045_, 1, v_a_5041_);
                if v_isShared_5044_ == 0 {
                    lean_ctor_set_tag(v___x_5043_, 1);
                    lean_ctor_set(v___x_5043_, 0, v___x_5045_);
                    v___x_5047_ = v___x_5043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
                    v___x_5047_ = v_reuseFailAlloc_5048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(
    mut v_msg_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5056_: *mut LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
        v_msg_5050_,
        v___y_5051_,
        v___y_5052_,
        v___y_5053_,
        v___y_5054_,
    );
    lean_dec(v___y_5054_);
    lean_dec_ref(v___y_5053_);
    lean_dec(v___y_5052_);
    lean_dec_ref(v___y_5051_);
    return v_res_5056_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    v___x_5058_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0;
    v___x_5059_ = l_Lean_stringToMessageData(v___x_5058_);
    return v___x_5059_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    v___x_5061_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2;
    v___x_5062_ = l_Lean_stringToMessageData(v___x_5061_);
    return v___x_5062_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5064_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4;
    v___x_5065_ = l_Lean_stringToMessageData(v___x_5064_);
    return v___x_5065_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    v___x_5067_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6;
    v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
    return v___x_5068_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(
    mut v_a_5069_: *mut LeanObject,
    mut v_x_5070_: *mut LeanObject,
    mut v_motiveParams_5071_: *mut LeanObject,
    mut v_motiveResultType_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
    mut v___y_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: u8 = 0;
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5086_ = lean_array_get_size(v_motiveParams_5071_);
                v___x_5087_ = lean_array_get_size(v_x_5070_);
                v___x_5088_ = lean_nat_dec_eq(v___x_5086_, v___x_5087_);
                if v___x_5088_ == 0 {
                    v___x_5089_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3);
                    v___x_5090_ = l_Nat_reprFast(v___x_5087_);
                    v___x_5091_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5091_, 0, v___x_5090_);
                    v___x_5092_ = l_Lean_MessageData_ofFormat(v___x_5091_);
                    v___x_5093_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5093_, 0, v___x_5089_);
                    lean_ctor_set(v___x_5093_, 1, v___x_5092_);
                    v___x_5094_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5);
                    v___x_5095_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5095_, 0, v___x_5093_);
                    lean_ctor_set(v___x_5095_, 1, v___x_5094_);
                    v___x_5096_ = l_Nat_reprFast(v___x_5086_);
                    v___x_5097_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5097_, 0, v___x_5096_);
                    v___x_5098_ = l_Lean_MessageData_ofFormat(v___x_5097_);
                    v___x_5099_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5099_, 0, v___x_5095_);
                    lean_ctor_set(v___x_5099_, 1, v___x_5098_);
                    v___x_5100_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7);
                    v___x_5101_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5101_, 0, v___x_5099_);
                    lean_ctor_set(v___x_5101_, 1, v___x_5100_);
                    v___x_5102_ = l_Lean_indentExpr(v_a_5069_);
                    v___x_5103_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5103_, 0, v___x_5101_);
                    lean_ctor_set(v___x_5103_, 1, v___x_5102_);
                    v___x_5104_ =
                        l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                            v___x_5103_,
                            v___y_5073_,
                            v___y_5074_,
                            v___y_5075_,
                            v___y_5076_,
                        );
                    return v___x_5104_;
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5079_ = l_Lean_Expr_isSort(v_motiveResultType_5072_);
                if v___x_5079_ == 0 {
                    v___x_5080_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1);
                    v___x_5081_ = l_Lean_indentExpr(v_a_5069_);
                    v___x_5082_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5082_, 0, v___x_5080_);
                    lean_ctor_set(v___x_5082_, 1, v___x_5081_);
                    v___x_5083_ =
                        l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                            v___x_5082_,
                            v___y_5073_,
                            v___y_5074_,
                            v___y_5075_,
                            v___y_5076_,
                        );
                    return v___x_5083_;
                } else {
                    lean_dec_ref(v_a_5069_);
                    v___x_5084_ = lean_box(0);
                    v___x_5085_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5085_, 0, v___x_5084_);
                    return v___x_5085_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(
    mut v_a_5105_: *mut LeanObject,
    mut v_x_5106_: *mut LeanObject,
    mut v_motiveParams_5107_: *mut LeanObject,
    mut v_motiveResultType_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5114_: *mut LeanObject = core::ptr::null_mut();
    v_res_5114_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(
        v_a_5105_,
        v_x_5106_,
        v_motiveParams_5107_,
        v_motiveResultType_5108_,
        v___y_5109_,
        v___y_5110_,
        v___y_5111_,
        v___y_5112_,
    );
    lean_dec(v___y_5112_);
    lean_dec_ref(v___y_5111_);
    lean_dec(v___y_5110_);
    lean_dec_ref(v___y_5109_);
    lean_dec_ref(v_motiveResultType_5108_);
    lean_dec_ref(v_motiveParams_5107_);
    lean_dec_ref(v_x_5106_);
    return v_res_5114_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(
    mut v_xs_5115_: *mut LeanObject,
    mut v_v_5116_: *mut LeanObject,
    mut v_i_5117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: u8 = 0;
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5118_ = lean_array_get_size(v_xs_5115_);
                v___x_5119_ = lean_nat_dec_lt(v_i_5117_, v___x_5118_);
                if v___x_5119_ == 0 {
                    lean_dec(v_i_5117_);
                    v___x_5120_ = lean_box(0);
                    return v___x_5120_;
                } else {
                    v___x_5121_ = lean_array_fget_borrowed(v_xs_5115_, v_i_5117_);
                    v___x_5122_ = lean_expr_eqv(v___x_5121_, v_v_5116_);
                    if v___x_5122_ == 0 {
                        v___x_5123_ = lean_unsigned_to_nat(1);
                        v___x_5124_ = lean_nat_add(v_i_5117_, v___x_5123_);
                        lean_dec(v_i_5117_);
                        v_i_5117_ = v___x_5124_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5126_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5126_, 0, v_i_5117_);
                        return v___x_5126_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(
    mut v_xs_5127_: *mut LeanObject,
    mut v_v_5128_: *mut LeanObject,
    mut v_i_5129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5130_: *mut LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_5127_, v_v_5128_, v_i_5129_);
    lean_dec_ref(v_v_5128_);
    lean_dec_ref(v_xs_5127_);
    return v_res_5130_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(
    mut v_xs_5131_: *mut LeanObject,
    mut v_v_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    v___x_5133_ = lean_unsigned_to_nat(0);
    v___x_5134_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_5131_, v_v_5132_, v___x_5133_);
    return v___x_5134_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(
    mut v_xs_5135_: *mut LeanObject,
    mut v_v_5136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5137_: *mut LeanObject = core::ptr::null_mut();
    v_res_5137_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_5135_, v_v_5136_);
    lean_dec_ref(v_v_5136_);
    lean_dec_ref(v_xs_5135_);
    return v_res_5137_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(
    mut v_xs_5138_: *mut LeanObject,
    mut v_v_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5145_: u8 = 0;
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5140_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_5138_, v_v_5139_);
                if lean_obj_tag(v___x_5140_) == 0 {
                    v___x_5141_ = lean_box(0);
                    return v___x_5141_;
                } else {
                    v_val_5142_ = lean_ctor_get(v___x_5140_, 0);
                    v_isSharedCheck_5149_ = (!lean_is_exclusive(v___x_5140_)) as u8;
                    if v_isSharedCheck_5149_ == 0 {
                        v___x_5144_ = v___x_5140_;
                        v_isShared_5145_ = v_isSharedCheck_5149_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5142_);
                        lean_dec(v___x_5140_);
                        v___x_5144_ = lean_box(0);
                        v_isShared_5145_ = v_isSharedCheck_5149_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5145_ == 0 {
                    v___x_5147_ = v___x_5144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_val_5142_);
                    v___x_5147_ = v_reuseFailAlloc_5148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(
    mut v_xs_5150_: *mut LeanObject,
    mut v_v_5151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5152_: *mut LeanObject = core::ptr::null_mut();
    v_res_5152_ =
        l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_5150_, v_v_5151_);
    lean_dec_ref(v_v_5151_);
    lean_dec_ref(v_xs_5150_);
    return v_res_5152_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    v___x_5154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0;
    v___x_5155_ = l_Lean_stringToMessageData(v___x_5154_);
    return v___x_5155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(
    mut v_xs_5156_: *mut LeanObject,
    mut v_a_5157_: *mut LeanObject,
    mut v_sz_5158_: usize,
    mut v_i_5159_: usize,
    mut v_bs_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
    mut v___y_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5166_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: usize = 0;
    let mut v___x_5174_: usize = 0;
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5186_: u8 = 0;
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_val_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5166_ = lean_usize_dec_lt(v_i_5159_, v_sz_5158_);
                if v___x_5166_ == 0 {
                    lean_dec_ref(v_a_5157_);
                    v___x_5167_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5167_, 0, v_bs_5160_);
                    return v___x_5167_;
                } else {
                    v_v_5168_ = lean_array_uget(v_bs_5160_, v_i_5159_);
                    v___x_5169_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5170_ = lean_array_uset(v_bs_5160_, v_i_5159_, v___x_5169_);
                    v___x_5177_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(
                        v_xs_5156_, v_v_5168_,
                    );
                    lean_dec(v_v_5168_);
                    if lean_obj_tag(v___x_5177_) == 0 {
                        v___x_5178_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
                        lean_inc_ref(v_a_5157_);
                        v___x_5179_ = l_Lean_indentExpr(v_a_5157_);
                        v___x_5180_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5180_, 0, v___x_5178_);
                        lean_ctor_set(v___x_5180_, 1, v___x_5179_);
                        v___x_5181_ =
                            l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                                v___x_5180_,
                                v___y_5161_,
                                v___y_5162_,
                                v___y_5163_,
                                v___y_5164_,
                            );
                        if lean_obj_tag(v___x_5181_) == 0 {
                            v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
                            lean_inc(v_a_5182_);
                            lean_dec_ref_known(v___x_5181_, 1);
                            v_a_5172_ = v_a_5182_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_bs_x27_5170_);
                            lean_dec_ref(v_a_5157_);
                            v_a_5183_ = lean_ctor_get(v___x_5181_, 0);
                            v_isSharedCheck_5190_ = (!lean_is_exclusive(v___x_5181_)) as u8;
                            if v_isSharedCheck_5190_ == 0 {
                                v___x_5185_ = v___x_5181_;
                                v_isShared_5186_ = v_isSharedCheck_5190_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_5183_);
                                lean_dec(v___x_5181_);
                                v___x_5185_ = lean_box(0);
                                v_isShared_5186_ = v_isSharedCheck_5190_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_val_5191_ = lean_ctor_get(v___x_5177_, 0);
                        lean_inc(v_val_5191_);
                        lean_dec_ref_known(v___x_5177_, 1);
                        v_a_5172_ = v_val_5191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5173_ = 1usize;
                v___x_5174_ = lean_usize_add(v_i_5159_, v___x_5173_);
                v___x_5175_ = lean_array_uset(v_bs_x27_5170_, v_i_5159_, v_a_5172_);
                v_i_5159_ = v___x_5174_;
                v_bs_5160_ = v___x_5175_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5186_ == 0 {
                    v___x_5188_ = v___x_5185_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
                    v___x_5188_ = v_reuseFailAlloc_5189_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(
    mut v_xs_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
    mut v_sz_5194_: *mut LeanObject,
    mut v_i_5195_: *mut LeanObject,
    mut v_bs_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5202_: usize = 0;
    let mut v_i_boxed_5203_: usize = 0;
    let mut v_res_5204_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5202_ = lean_unbox_usize(v_sz_5194_);
    lean_dec(v_sz_5194_);
    v_i_boxed_5203_ = lean_unbox_usize(v_i_5195_);
    lean_dec(v_i_5195_);
    v_res_5204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_5192_, v_a_5193_, v_sz_boxed_5202_, v_i_boxed_5203_, v_bs_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
    lean_dec(v___y_5200_);
    lean_dec_ref(v___y_5199_);
    lean_dec(v___y_5198_);
    lean_dec_ref(v___y_5197_);
    lean_dec_ref(v_xs_5192_);
    return v_res_5204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(
    mut v_a_5205_: *mut LeanObject,
    mut v_as_5206_: *mut LeanObject,
    mut v_i_5207_: usize,
    mut v_stop_5208_: usize,
) -> u8 {
    let mut v___x_5209_: u8 = 0;
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5212_: usize = 0;
    let mut v___x_5213_: usize = 0;
    let mut v___x_5215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5209_ = lean_usize_dec_eq(v_i_5207_, v_stop_5208_);
                if v___x_5209_ == 0 {
                    v___x_5210_ = lean_array_uget_borrowed(v_as_5206_, v_i_5207_);
                    v___x_5211_ = lean_expr_eqv(v_a_5205_, v___x_5210_);
                    if v___x_5211_ == 0 {
                        v___x_5212_ = 1usize;
                        v___x_5213_ = lean_usize_add(v_i_5207_, v___x_5212_);
                        v_i_5207_ = v___x_5213_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5211_;
                    }
                } else {
                    v___x_5215_ = 0;
                    return v___x_5215_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(
    mut v_a_5216_: *mut LeanObject,
    mut v_as_5217_: *mut LeanObject,
    mut v_i_5218_: *mut LeanObject,
    mut v_stop_5219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5220_: usize = 0;
    let mut v_stop_boxed_5221_: usize = 0;
    let mut v_res_5222_: u8 = 0;
    let mut v_r_5223_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5220_ = lean_unbox_usize(v_i_5218_);
    lean_dec(v_i_5218_);
    v_stop_boxed_5221_ = lean_unbox_usize(v_stop_5219_);
    lean_dec(v_stop_5219_);
    v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_5216_, v_as_5217_, v_i_boxed_5220_, v_stop_boxed_5221_);
    lean_dec_ref(v_as_5217_);
    lean_dec_ref(v_a_5216_);
    v_r_5223_ = lean_box((v_res_5222_) as usize);
    return v_r_5223_;
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(
    mut v_as_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
) -> u8 {
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: u8 = 0;
    v___x_5226_ = lean_unsigned_to_nat(0);
    v___x_5227_ = lean_array_get_size(v_as_5224_);
    v___x_5228_ = lean_nat_dec_lt(v___x_5226_, v___x_5227_);
    if v___x_5228_ == 0 {
        return v___x_5228_;
    } else {
        if v___x_5228_ == 0 {
            return v___x_5228_;
        } else {
            let mut v___x_5229_: usize = 0;
            let mut v___x_5230_: usize = 0;
            let mut v___x_5231_: u8 = 0;
            v___x_5229_ = 0usize;
            v___x_5230_ = lean_usize_of_nat(v___x_5227_);
            v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_5225_, v_as_5224_, v___x_5229_, v___x_5230_);
            return v___x_5231_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(
    mut v_as_5232_: *mut LeanObject,
    mut v_a_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5234_: u8 = 0;
    let mut v_r_5235_: *mut LeanObject = core::ptr::null_mut();
    v_res_5234_ =
        l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v_as_5232_, v_a_5233_);
    lean_dec_ref(v_a_5233_);
    lean_dec_ref(v_as_5232_);
    v_r_5235_ = lean_box((v_res_5234_) as usize);
    return v_r_5235_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(
    mut v_upperBound_5236_: *mut LeanObject,
    mut v_xs_5237_: *mut LeanObject,
    mut v_motive_5238_: *mut LeanObject,
    mut v___x_5239_: *mut LeanObject,
    mut v_baseDeclName_x3f_5240_: *mut LeanObject,
    mut v___x_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
    mut v_b_5243_: *mut LeanObject,
    mut v___y_5244_: *mut LeanObject,
    mut v___y_5245_: *mut LeanObject,
    mut v___y_5246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: u8 = 0;
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: u8 = 0;
    let mut v___x_5257_: u8 = 0;
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: u8 = 0;
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5282_: u8 = 0;
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5253_ = lean_nat_dec_lt(v_a_5242_, v_upperBound_5236_);
                if v___x_5253_ == 0 {
                    lean_dec(v_a_5242_);
                    lean_dec_ref(v___x_5241_);
                    lean_dec(v_baseDeclName_x3f_5240_);
                    v___x_5254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5254_, 0, v_b_5243_);
                    return v___x_5254_;
                } else {
                    v___x_5255_ = lean_array_fget_borrowed(v_xs_5237_, v_a_5242_);
                    v___x_5256_ = lean_expr_eqv(v___x_5255_, v_motive_5238_);
                    if v___x_5256_ == 0 {
                        v___x_5257_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(
                            v___x_5239_,
                            v___x_5255_,
                        );
                        if v___x_5257_ == 0 {
                            v___x_5258_ = l_Lean_Expr_fvarId_x21(v___x_5255_);
                            v___x_5259_ = l_Lean_FVarId_getDecl___redArg(
                                v___x_5258_,
                                v___y_5244_,
                                v___y_5245_,
                                v___y_5246_,
                            );
                            if lean_obj_tag(v___x_5259_) == 0 {
                                v_a_5260_ = lean_ctor_get(v___x_5259_, 0);
                                lean_inc(v_a_5260_);
                                lean_dec_ref_known(v___x_5259_, 1);
                                v___x_5261_ = l_Lean_LocalDecl_binderInfo(v_a_5260_);
                                v___x_5262_ = l_Lean_BinderInfo_isExplicit(v___x_5261_);
                                if v___x_5262_ == 0 {
                                    lean_dec(v_a_5260_);
                                    v_a_5249_ = v_b_5243_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5263_ = lean_unsigned_to_nat(0);
                                    v___x_5264_ = l_Lean_LocalDecl_type(v_a_5260_);
                                    v___x_5265_ = l_Lean_Meta_altArity(
                                        v_motive_5238_,
                                        v___x_5263_,
                                        v___x_5264_,
                                    );
                                    lean_dec_ref(v___x_5264_);
                                    v_fst_5266_ = lean_ctor_get(v___x_5265_, 0);
                                    lean_inc(v_fst_5266_);
                                    v_snd_5267_ = lean_ctor_get(v___x_5265_, 1);
                                    lean_inc(v_snd_5267_);
                                    lean_dec_ref(v___x_5265_);
                                    v___x_5268_ = l_Lean_LocalDecl_userName(v_a_5260_);
                                    lean_dec(v_a_5260_);
                                    if lean_obj_tag(v_baseDeclName_x3f_5240_) == 0 {
                                        v___y_5270_ = v_baseDeclName_x3f_5240_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_val_5274_ = lean_ctor_get(v_baseDeclName_x3f_5240_, 0);
                                        lean_inc(v___x_5268_);
                                        lean_inc(v_val_5274_);
                                        v___x_5275_ = l_Lean_Name_append(v_val_5274_, v___x_5268_);
                                        lean_inc(v___x_5275_);
                                        lean_inc_ref(v___x_5241_);
                                        v___x_5276_ = l_Lean_Environment_contains(
                                            v___x_5241_,
                                            v___x_5275_,
                                            v___x_5262_,
                                        );
                                        if v___x_5276_ == 0 {
                                            lean_dec(v___x_5275_);
                                            v___x_5277_ = lean_box(0);
                                            v___y_5270_ = v___x_5277_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_5278_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_5278_, 0, v___x_5275_);
                                            v___y_5270_ = v___x_5278_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_b_5243_);
                                lean_dec(v_a_5242_);
                                lean_dec_ref(v___x_5241_);
                                lean_dec(v_baseDeclName_x3f_5240_);
                                v_a_5279_ = lean_ctor_get(v___x_5259_, 0);
                                v_isSharedCheck_5286_ = (!lean_is_exclusive(v___x_5259_)) as u8;
                                if v_isSharedCheck_5286_ == 0 {
                                    v___x_5281_ = v___x_5259_;
                                    v_isShared_5282_ = v_isSharedCheck_5286_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5279_);
                                    lean_dec(v___x_5259_);
                                    v___x_5281_ = lean_box(0);
                                    v_isShared_5282_ = v_isSharedCheck_5286_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_5249_ = v_b_5243_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5249_ = v_b_5243_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5250_ = lean_unsigned_to_nat(1);
                v___x_5251_ = lean_nat_add(v_a_5242_, v___x_5250_);
                lean_dec(v_a_5242_);
                v_a_5242_ = v___x_5251_;
                v_b_5243_ = v_a_5249_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5271_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_5271_, 0, v___x_5268_);
                lean_ctor_set(v___x_5271_, 1, v___y_5270_);
                lean_ctor_set(v___x_5271_, 2, v_fst_5266_);
                v___x_5272_ = (lean_unbox(v_snd_5267_) as u8);
                lean_dec(v_snd_5267_);
                lean_ctor_set_uint8(
                    v___x_5271_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5272_,
                );
                v___x_5273_ = lean_array_push(v_b_5243_, v___x_5271_);
                v_a_5249_ = v___x_5273_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_5282_ == 0 {
                    v___x_5284_ = v___x_5281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
                    v___x_5284_ = v_reuseFailAlloc_5285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(
    mut v_upperBound_5287_: *mut LeanObject,
    mut v_xs_5288_: *mut LeanObject,
    mut v_motive_5289_: *mut LeanObject,
    mut v___x_5290_: *mut LeanObject,
    mut v_baseDeclName_x3f_5291_: *mut LeanObject,
    mut v___x_5292_: *mut LeanObject,
    mut v_a_5293_: *mut LeanObject,
    mut v_b_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5299_: *mut LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(
        v_upperBound_5287_,
        v_xs_5288_,
        v_motive_5289_,
        v___x_5290_,
        v_baseDeclName_x3f_5291_,
        v___x_5292_,
        v_a_5293_,
        v_b_5294_,
        v___y_5295_,
        v___y_5296_,
        v___y_5297_,
    );
    lean_dec(v___y_5297_);
    lean_dec_ref(v___y_5296_);
    lean_dec_ref(v___y_5295_);
    lean_dec_ref(v___x_5290_);
    lean_dec_ref(v_motive_5289_);
    lean_dec_ref(v_xs_5288_);
    lean_dec(v_upperBound_5287_);
    return v_res_5299_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    v___x_5304_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2;
    v___x_5305_ = l_Lean_stringToMessageData(v___x_5304_);
    return v___x_5305_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(
    mut v_xs_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_elimExpr_5308_: *mut LeanObject,
    mut v_baseDeclName_x3f_5309_: *mut LeanObject,
    mut v_type_5310_: *mut LeanObject,
    mut v_x_5311_: *mut LeanObject,
    mut v_x_5312_: *mut LeanObject,
    mut v_x_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
    mut v___y_5316_: *mut LeanObject,
    mut v___y_5317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: u8 = 0;
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5333_: usize = 0;
    let mut v___x_5334_: usize = 0;
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5348_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut v_a_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5381_: u8 = 0;
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v_a_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5389_: u8 = 0;
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v_fn_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5311_) == 5 {
                    v_fn_5394_ = lean_ctor_get(v_x_5311_, 0);
                    lean_inc_ref(v_fn_5394_);
                    v_arg_5395_ = lean_ctor_get(v_x_5311_, 1);
                    lean_inc_ref(v_arg_5395_);
                    lean_dec_ref_known(v_x_5311_, 2);
                    v___x_5396_ = lean_array_set(v_x_5312_, v_x_5313_, v_arg_5395_);
                    v___x_5397_ = lean_unsigned_to_nat(1);
                    v___x_5398_ = lean_nat_sub(v_x_5313_, v___x_5397_);
                    lean_dec(v_x_5313_);
                    v_x_5311_ = v_fn_5394_;
                    v_x_5312_ = v___x_5396_;
                    v_x_5313_ = v___x_5398_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_5313_);
                    v___f_5400_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1;
                    v___x_5413_ = l_Lean_Expr_isFVar(v_x_5311_);
                    if v___x_5413_ == 0 {
                        lean_dec_ref(v_x_5312_);
                        lean_dec_ref(v_x_5311_);
                        lean_dec(v_baseDeclName_x3f_5309_);
                        lean_dec_ref(v_elimExpr_5308_);
                        lean_dec_ref(v_a_5307_);
                        v___x_5414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
                        v___x_5415_ = l_Lean_indentExpr(v_type_5310_);
                        v___x_5416_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5416_, 0, v___x_5414_);
                        lean_ctor_set(v___x_5416_, 1, v___x_5415_);
                        v___x_5417_ =
                            l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                                v___x_5416_,
                                v___y_5314_,
                                v___y_5315_,
                                v___y_5316_,
                                v___y_5317_,
                            );
                        v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
                        v_isSharedCheck_5425_ = (!lean_is_exclusive(v___x_5417_)) as u8;
                        if v_isSharedCheck_5425_ == 0 {
                            v___x_5420_ = v___x_5417_;
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5418_);
                            lean_dec(v___x_5417_);
                            v___x_5420_ = lean_box(0);
                            v_isShared_5421_ = v_isSharedCheck_5425_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_5310_);
                        v___y_5402_ = v___y_5314_;
                        v___y_5403_ = v___y_5315_;
                        v___y_5404_ = v___y_5316_;
                        v___y_5405_ = v___y_5317_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_5320_);
                lean_inc_ref(v___y_5323_);
                lean_inc(v___y_5321_);
                lean_inc_ref(v___y_5322_);
                lean_inc_ref(v_x_5311_);
                v___x_5326_ = lean_infer_type(
                    v_x_5311_,
                    v___y_5322_,
                    v___y_5321_,
                    v___y_5323_,
                    v___y_5320_,
                );
                if lean_obj_tag(v___x_5326_) == 0 {
                    v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
                    lean_inc_n(v_a_5327_, 2);
                    lean_dec_ref_known(v___x_5326_, 1);
                    lean_inc_ref(v_x_5312_);
                    v___f_5328_ = lean_alloc_closure(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                    lean_closure_set(v___f_5328_, 0, v_a_5327_);
                    lean_closure_set(v___f_5328_, 1, v_x_5312_);
                    v___x_5329_ = 0;
                    v___x_5330_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_5327_, v___f_5328_, v___x_5329_, v___x_5329_, v___y_5322_, v___y_5321_, v___y_5323_, v___y_5320_);
                    if lean_obj_tag(v___x_5330_) == 0 {
                        lean_dec_ref_known(v___x_5330_, 1);
                        v___x_5331_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(
                            v_xs_5306_, v_x_5311_,
                        );
                        if lean_obj_tag(v___x_5331_) == 1 {
                            v_val_5332_ = lean_ctor_get(v___x_5331_, 0);
                            lean_inc(v_val_5332_);
                            lean_dec_ref_known(v___x_5331_, 1);
                            v_sz_5333_ = lean_array_size(v___y_5324_);
                            v___x_5334_ = 0usize;
                            lean_inc_ref(v___y_5324_);
                            lean_inc_ref(v_a_5307_);
                            v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_5306_, v_a_5307_, v_sz_5333_, v___x_5334_, v___y_5324_, v___y_5322_, v___y_5321_, v___y_5323_, v___y_5320_);
                            if lean_obj_tag(v___x_5335_) == 0 {
                                v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
                                lean_inc(v_a_5336_);
                                lean_dec_ref_known(v___x_5335_, 1);
                                v___x_5337_ = lean_st_ref_get(v___y_5320_);
                                v_lower_5338_ = lean_ctor_get(v___y_5325_, 0);
                                lean_inc(v_lower_5338_);
                                v_upper_5339_ = lean_ctor_get(v___y_5325_, 1);
                                lean_inc(v_upper_5339_);
                                lean_dec_ref(v___y_5325_);
                                v_env_5340_ = lean_ctor_get(v___x_5337_, 0);
                                lean_inc_ref(v_env_5340_);
                                lean_dec(v___x_5337_);
                                v___x_5341_ = lean_array_get_size(v_xs_5306_);
                                v___x_5342_ = lean_unsigned_to_nat(0);
                                v___x_5343_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0;
                                v___x_5344_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_5341_, v_xs_5306_, v_x_5311_, v___y_5324_, v_baseDeclName_x3f_5309_, v_env_5340_, v___x_5342_, v___x_5343_, v___y_5322_, v___y_5323_, v___y_5320_);
                                lean_dec_ref(v___y_5324_);
                                lean_dec_ref(v_x_5311_);
                                if lean_obj_tag(v___x_5344_) == 0 {
                                    v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
                                    v_isSharedCheck_5357_ = (!lean_is_exclusive(v___x_5344_)) as u8;
                                    if v_isSharedCheck_5357_ == 0 {
                                        v___x_5347_ = v___x_5344_;
                                        v_isShared_5348_ = v_isSharedCheck_5357_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5345_);
                                        lean_dec(v___x_5344_);
                                        v___x_5347_ = lean_box(0);
                                        v_isShared_5348_ = v_isSharedCheck_5357_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_upper_5339_);
                                    lean_dec(v_lower_5338_);
                                    lean_dec(v_a_5336_);
                                    lean_dec(v_val_5332_);
                                    lean_dec_ref(v_x_5312_);
                                    lean_dec_ref(v_elimExpr_5308_);
                                    lean_dec_ref(v_a_5307_);
                                    v_a_5358_ = lean_ctor_get(v___x_5344_, 0);
                                    v_isSharedCheck_5365_ = (!lean_is_exclusive(v___x_5344_)) as u8;
                                    if v_isSharedCheck_5365_ == 0 {
                                        v___x_5360_ = v___x_5344_;
                                        v_isShared_5361_ = v_isSharedCheck_5365_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5358_);
                                        lean_dec(v___x_5344_);
                                        v___x_5360_ = lean_box(0);
                                        v_isShared_5361_ = v_isSharedCheck_5365_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_5332_);
                                lean_dec_ref(v___y_5325_);
                                lean_dec_ref(v___y_5324_);
                                lean_dec_ref(v_x_5312_);
                                lean_dec_ref(v_x_5311_);
                                lean_dec(v_baseDeclName_x3f_5309_);
                                lean_dec_ref(v_elimExpr_5308_);
                                lean_dec_ref(v_a_5307_);
                                v_a_5366_ = lean_ctor_get(v___x_5335_, 0);
                                v_isSharedCheck_5373_ = (!lean_is_exclusive(v___x_5335_)) as u8;
                                if v_isSharedCheck_5373_ == 0 {
                                    v___x_5368_ = v___x_5335_;
                                    v_isShared_5369_ = v_isSharedCheck_5373_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5366_);
                                    lean_dec(v___x_5335_);
                                    v___x_5368_ = lean_box(0);
                                    v_isShared_5369_ = v_isSharedCheck_5373_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5331_);
                            lean_dec_ref(v___y_5325_);
                            lean_dec_ref(v___y_5324_);
                            lean_dec_ref(v_x_5312_);
                            lean_dec_ref(v_x_5311_);
                            lean_dec(v_baseDeclName_x3f_5309_);
                            lean_dec_ref(v_elimExpr_5308_);
                            v___x_5374_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
                            v___x_5375_ = l_Lean_indentExpr(v_a_5307_);
                            v___x_5376_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5376_, 0, v___x_5374_);
                            lean_ctor_set(v___x_5376_, 1, v___x_5375_);
                            v___x_5377_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_5376_, v___y_5322_, v___y_5321_, v___y_5323_, v___y_5320_);
                            return v___x_5377_;
                        }
                    } else {
                        lean_dec_ref(v___y_5325_);
                        lean_dec_ref(v___y_5324_);
                        lean_dec_ref(v_x_5312_);
                        lean_dec_ref(v_x_5311_);
                        lean_dec(v_baseDeclName_x3f_5309_);
                        lean_dec_ref(v_elimExpr_5308_);
                        lean_dec_ref(v_a_5307_);
                        v_a_5378_ = lean_ctor_get(v___x_5330_, 0);
                        v_isSharedCheck_5385_ = (!lean_is_exclusive(v___x_5330_)) as u8;
                        if v_isSharedCheck_5385_ == 0 {
                            v___x_5380_ = v___x_5330_;
                            v_isShared_5381_ = v_isSharedCheck_5385_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5378_);
                            lean_dec(v___x_5330_);
                            v___x_5380_ = lean_box(0);
                            v_isShared_5381_ = v_isSharedCheck_5385_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5325_);
                    lean_dec_ref(v___y_5324_);
                    lean_dec_ref(v_x_5312_);
                    lean_dec_ref(v_x_5311_);
                    lean_dec(v_baseDeclName_x3f_5309_);
                    lean_dec_ref(v_elimExpr_5308_);
                    lean_dec_ref(v_a_5307_);
                    v_a_5386_ = lean_ctor_get(v___x_5326_, 0);
                    v_isSharedCheck_5393_ = (!lean_is_exclusive(v___x_5326_)) as u8;
                    if v_isSharedCheck_5393_ == 0 {
                        v___x_5388_ = v___x_5326_;
                        v_isShared_5389_ = v_isSharedCheck_5393_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5386_);
                        lean_dec(v___x_5326_);
                        v___x_5388_ = lean_box(0);
                        v_isShared_5389_ = v_isSharedCheck_5393_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5349_ = l_Array_toSubarray___redArg(v_x_5312_, v_lower_5338_, v_upper_5339_);
                v_start_5350_ = lean_ctor_get(v___x_5349_, 1);
                lean_inc(v_start_5350_);
                v_stop_5351_ = lean_ctor_get(v___x_5349_, 2);
                lean_inc(v_stop_5351_);
                lean_dec_ref(v___x_5349_);
                v___x_5352_ = lean_nat_sub(v_stop_5351_, v_start_5350_);
                lean_dec(v_start_5350_);
                lean_dec(v_stop_5351_);
                v___x_5353_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_5353_, 0, v_elimExpr_5308_);
                lean_ctor_set(v___x_5353_, 1, v_a_5307_);
                lean_ctor_set(v___x_5353_, 2, v_val_5332_);
                lean_ctor_set(v___x_5353_, 3, v_a_5336_);
                lean_ctor_set(v___x_5353_, 4, v_a_5345_);
                lean_ctor_set(v___x_5353_, 5, v___x_5352_);
                if v_isShared_5348_ == 0 {
                    lean_ctor_set(v___x_5347_, 0, v___x_5353_);
                    v___x_5355_ = v___x_5347_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5355_;
            }
            4 => {
                if v_isShared_5361_ == 0 {
                    v___x_5363_ = v___x_5360_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5363_;
            }
            6 => {
                if v_isShared_5369_ == 0 {
                    v___x_5371_ = v___x_5368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
                    v___x_5371_ = v_reuseFailAlloc_5372_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5371_;
            }
            8 => {
                if v_isShared_5381_ == 0 {
                    v___x_5383_ = v___x_5380_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
                    v___x_5383_ = v_reuseFailAlloc_5384_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5383_;
            }
            10 => {
                if v_isShared_5389_ == 0 {
                    v___x_5391_ = v___x_5388_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
                    v___x_5391_ = v_reuseFailAlloc_5392_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5391_;
            }
            12 => {
                v___x_5406_ = l_Array_takeWhile___redArg(v___f_5400_, v_x_5312_);
                v___x_5407_ = lean_array_get_size(v___x_5406_);
                v___x_5408_ = lean_unsigned_to_nat(0);
                v___x_5409_ = lean_array_get_size(v_x_5312_);
                v___x_5410_ = lean_nat_dec_le(v___x_5407_, v___x_5408_);
                if v___x_5410_ == 0 {
                    v___x_5411_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5411_, 0, v___x_5407_);
                    lean_ctor_set(v___x_5411_, 1, v___x_5409_);
                    v___y_5320_ = v___y_5405_;
                    v___y_5321_ = v___y_5403_;
                    v___y_5322_ = v___y_5402_;
                    v___y_5323_ = v___y_5404_;
                    v___y_5324_ = v___x_5406_;
                    v___y_5325_ = v___x_5411_;
                    state = 1;
                    continue;
                } else {
                    v___x_5412_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5412_, 0, v___x_5408_);
                    lean_ctor_set(v___x_5412_, 1, v___x_5409_);
                    v___y_5320_ = v___y_5405_;
                    v___y_5321_ = v___y_5403_;
                    v___y_5322_ = v___y_5402_;
                    v___y_5323_ = v___y_5404_;
                    v___y_5324_ = v___x_5406_;
                    v___y_5325_ = v___x_5412_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                if v_isShared_5421_ == 0 {
                    v___x_5423_ = v___x_5420_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
                    v___x_5423_ = v_reuseFailAlloc_5424_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(
    mut v_xs_5426_: *mut LeanObject,
    mut v_a_5427_: *mut LeanObject,
    mut v_elimExpr_5428_: *mut LeanObject,
    mut v_baseDeclName_x3f_5429_: *mut LeanObject,
    mut v_type_5430_: *mut LeanObject,
    mut v_x_5431_: *mut LeanObject,
    mut v_x_5432_: *mut LeanObject,
    mut v_x_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5439_: *mut LeanObject = core::ptr::null_mut();
    v_res_5439_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(
        v_xs_5426_,
        v_a_5427_,
        v_elimExpr_5428_,
        v_baseDeclName_x3f_5429_,
        v_type_5430_,
        v_x_5431_,
        v_x_5432_,
        v_x_5433_,
        v___y_5434_,
        v___y_5435_,
        v___y_5436_,
        v___y_5437_,
    );
    lean_dec(v___y_5437_);
    lean_dec_ref(v___y_5436_);
    lean_dec(v___y_5435_);
    lean_dec_ref(v___y_5434_);
    lean_dec_ref(v_xs_5426_);
    return v_res_5439_;
}
pub unsafe fn _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5441_: *mut LeanObject = core::ptr::null_mut();
    v___x_5440_ = lean_box(0);
    v_dummy_5441_ = l_Lean_Expr_sort___override(v___x_5440_);
    return v_dummy_5441_;
}
pub unsafe fn l_Lean_Meta_getElimExprInfo___lam__0(
    mut v_a_5442_: *mut LeanObject,
    mut v_elimExpr_5443_: *mut LeanObject,
    mut v_baseDeclName_x3f_5444_: *mut LeanObject,
    mut v_xs_5445_: *mut LeanObject,
    mut v_type_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
    mut v___y_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_5452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once),
        _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0,
    );
    v_nargs_5453_ = l_Lean_Expr_getAppNumArgs(v_type_5446_);
    lean_inc(v_nargs_5453_);
    v___x_5454_ = lean_mk_array(v_nargs_5453_, v_dummy_5452_);
    v___x_5455_ = lean_unsigned_to_nat(1);
    v___x_5456_ = lean_nat_sub(v_nargs_5453_, v___x_5455_);
    lean_dec(v_nargs_5453_);
    lean_inc_ref(v_type_5446_);
    v___x_5457_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(
        v_xs_5445_,
        v_a_5442_,
        v_elimExpr_5443_,
        v_baseDeclName_x3f_5444_,
        v_type_5446_,
        v_type_5446_,
        v___x_5454_,
        v___x_5456_,
        v___y_5447_,
        v___y_5448_,
        v___y_5449_,
        v___y_5450_,
    );
    return v___x_5457_;
}
pub unsafe fn l_Lean_Meta_getElimExprInfo___lam__0___boxed(
    mut v_a_5458_: *mut LeanObject,
    mut v_elimExpr_5459_: *mut LeanObject,
    mut v_baseDeclName_x3f_5460_: *mut LeanObject,
    mut v_xs_5461_: *mut LeanObject,
    mut v_type_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
    mut v___y_5466_: *mut LeanObject,
    mut v___y_5467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5468_: *mut LeanObject = core::ptr::null_mut();
    v_res_5468_ = l_Lean_Meta_getElimExprInfo___lam__0(
        v_a_5458_,
        v_elimExpr_5459_,
        v_baseDeclName_x3f_5460_,
        v_xs_5461_,
        v_type_5462_,
        v___y_5463_,
        v___y_5464_,
        v___y_5465_,
        v___y_5466_,
    );
    lean_dec(v___y_5466_);
    lean_dec_ref(v___y_5465_);
    lean_dec(v___y_5464_);
    lean_dec_ref(v___y_5463_);
    lean_dec_ref(v_xs_5461_);
    return v_res_5468_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0() -> f64
{
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: f64 = 0.0;
    v___x_5469_ = lean_unsigned_to_nat(0);
    v___x_5470_ = lean_float_of_nat(v___x_5469_);
    return v___x_5470_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(
    mut v_cls_5474_: *mut LeanObject,
    mut v_msg_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v_tid_5500_: u64 = 0;
    let mut v_traces_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: f64 = 0.0;
    let mut v___x_5507_: u8 = 0;
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5481_ = lean_ctor_get(v___y_5478_, 5);
                v___x_5482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_);
                v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
                v_isSharedCheck_5527_ = (!lean_is_exclusive(v___x_5482_)) as u8;
                if v_isSharedCheck_5527_ == 0 {
                    v___x_5485_ = v___x_5482_;
                    v_isShared_5486_ = v_isSharedCheck_5527_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5483_);
                    lean_dec(v___x_5482_);
                    v___x_5485_ = lean_box(0);
                    v_isShared_5486_ = v_isSharedCheck_5527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5487_ = lean_st_ref_take(v___y_5479_);
                v_traceState_5488_ = lean_ctor_get(v___x_5487_, 4);
                v_env_5489_ = lean_ctor_get(v___x_5487_, 0);
                v_nextMacroScope_5490_ = lean_ctor_get(v___x_5487_, 1);
                v_ngen_5491_ = lean_ctor_get(v___x_5487_, 2);
                v_auxDeclNGen_5492_ = lean_ctor_get(v___x_5487_, 3);
                v_cache_5493_ = lean_ctor_get(v___x_5487_, 5);
                v_messages_5494_ = lean_ctor_get(v___x_5487_, 6);
                v_infoState_5495_ = lean_ctor_get(v___x_5487_, 7);
                v_snapshotTasks_5496_ = lean_ctor_get(v___x_5487_, 8);
                v_isSharedCheck_5526_ = (!lean_is_exclusive(v___x_5487_)) as u8;
                if v_isSharedCheck_5526_ == 0 {
                    v___x_5498_ = v___x_5487_;
                    v_isShared_5499_ = v_isSharedCheck_5526_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5496_);
                    lean_inc(v_infoState_5495_);
                    lean_inc(v_messages_5494_);
                    lean_inc(v_cache_5493_);
                    lean_inc(v_traceState_5488_);
                    lean_inc(v_auxDeclNGen_5492_);
                    lean_inc(v_ngen_5491_);
                    lean_inc(v_nextMacroScope_5490_);
                    lean_inc(v_env_5489_);
                    lean_dec(v___x_5487_);
                    v___x_5498_ = lean_box(0);
                    v_isShared_5499_ = v_isSharedCheck_5526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5500_ = lean_ctor_get_uint64(
                    v_traceState_5488_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5501_ = lean_ctor_get(v_traceState_5488_, 0);
                v_isSharedCheck_5525_ = (!lean_is_exclusive(v_traceState_5488_)) as u8;
                if v_isSharedCheck_5525_ == 0 {
                    v___x_5503_ = v_traceState_5488_;
                    v_isShared_5504_ = v_isSharedCheck_5525_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5501_);
                    lean_dec(v_traceState_5488_);
                    v___x_5503_ = lean_box(0);
                    v_isShared_5504_ = v_isSharedCheck_5525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5505_ = lean_box(0);
                v___x_5506_ = lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0,
                );
                v___x_5507_ = 0;
                v___x_5508_ =
                    l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1;
                v___x_5509_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5509_, 0, v_cls_5474_);
                lean_ctor_set(v___x_5509_, 1, v___x_5505_);
                lean_ctor_set(v___x_5509_, 2, v___x_5508_);
                lean_ctor_set_float(
                    v___x_5509_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5506_,
                );
                lean_ctor_set_float(
                    v___x_5509_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5506_,
                );
                lean_ctor_set_uint8(
                    v___x_5509_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5507_,
                );
                v___x_5510_ =
                    l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2;
                v___x_5511_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5511_, 0, v___x_5509_);
                lean_ctor_set(v___x_5511_, 1, v_a_5483_);
                lean_ctor_set(v___x_5511_, 2, v___x_5510_);
                lean_inc(v_ref_5481_);
                v___x_5512_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5512_, 0, v_ref_5481_);
                lean_ctor_set(v___x_5512_, 1, v___x_5511_);
                v___x_5513_ = l_Lean_PersistentArray_push___redArg(v_traces_5501_, v___x_5512_);
                if v_isShared_5504_ == 0 {
                    lean_ctor_set(v___x_5503_, 0, v___x_5513_);
                    v___x_5515_ = v___x_5503_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5513_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5524_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5500_,
                    );
                    v___x_5515_ = v_reuseFailAlloc_5524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5499_ == 0 {
                    lean_ctor_set(v___x_5498_, 4, v___x_5515_);
                    v___x_5517_ = v___x_5498_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_env_5489_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_nextMacroScope_5490_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_ngen_5491_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_auxDeclNGen_5492_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 4, v___x_5515_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 5, v_cache_5493_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_messages_5494_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 7, v_infoState_5495_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 8, v_snapshotTasks_5496_);
                    v___x_5517_ = v_reuseFailAlloc_5523_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5518_ = lean_st_ref_set(v___y_5479_, v___x_5517_);
                v___x_5519_ = lean_box(0);
                if v_isShared_5486_ == 0 {
                    lean_ctor_set(v___x_5485_, 0, v___x_5519_);
                    v___x_5521_ = v___x_5485_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5519_);
                    v___x_5521_ = v_reuseFailAlloc_5522_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(
    mut v_cls_5528_: *mut LeanObject,
    mut v_msg_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5535_: *mut LeanObject = core::ptr::null_mut();
    v_res_5535_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(
        v_cls_5528_,
        v_msg_5529_,
        v___y_5530_,
        v___y_5531_,
        v___y_5532_,
        v___y_5533_,
    );
    lean_dec(v___y_5533_);
    lean_dec_ref(v___y_5532_);
    lean_dec(v___y_5531_);
    lean_dec_ref(v___y_5530_);
    return v_res_5535_;
}
pub unsafe fn _init_l_Lean_Meta_getElimExprInfo___closed__5() -> *mut LeanObject {
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    v___x_5544_ = l_Lean_Meta_getElimExprInfo___closed__2;
    v___x_5545_ = l_Lean_Meta_getElimExprInfo___closed__4;
    v___x_5546_ = l_Lean_Name_append(v___x_5545_, v___x_5544_);
    return v___x_5546_;
}
pub unsafe fn _init_l_Lean_Meta_getElimExprInfo___closed__7() -> *mut LeanObject {
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    v___x_5548_ = l_Lean_Meta_getElimExprInfo___closed__6;
    v___x_5549_ = l_Lean_stringToMessageData(v___x_5548_);
    return v___x_5549_;
}
pub unsafe fn _init_l_Lean_Meta_getElimExprInfo___closed__9() -> *mut LeanObject {
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    v___x_5551_ = l_Lean_Meta_getElimExprInfo___closed__8;
    v___x_5552_ = l_Lean_stringToMessageData(v___x_5551_);
    return v___x_5552_;
}
pub unsafe fn l_Lean_Meta_getElimExprInfo(
    mut v_elimExpr_5553_: *mut LeanObject,
    mut v_baseDeclName_x3f_5554_: *mut LeanObject,
    mut v_a_5555_: *mut LeanObject,
    mut v_a_5556_: *mut LeanObject,
    mut v_a_5557_: *mut LeanObject,
    mut v_a_5558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5564_: u8 = 0;
    let mut v___f_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: u8 = 0;
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: u8 = 0;
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5587_: u8 = 0;
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_5558_);
                lean_inc_ref(v_a_5557_);
                lean_inc(v_a_5556_);
                lean_inc_ref(v_a_5555_);
                lean_inc_ref(v_elimExpr_5553_);
                v___x_5560_ =
                    lean_infer_type(v_elimExpr_5553_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_);
                if lean_obj_tag(v___x_5560_) == 0 {
                    v_options_5561_ = lean_ctor_get(v_a_5557_, 2);
                    v_a_5562_ = lean_ctor_get(v___x_5560_, 0);
                    lean_inc_n(v_a_5562_, 2);
                    lean_dec_ref_known(v___x_5560_, 1);
                    v_inheritedTraceOptions_5563_ = lean_ctor_get(v_a_5557_, 13);
                    v_hasTrace_5564_ = lean_ctor_get_uint8(
                        v_options_5561_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_inc_ref(v_elimExpr_5553_);
                    v___f_5565_ = lean_alloc_closure(
                        l_Lean_Meta_getElimExprInfo___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    lean_closure_set(v___f_5565_, 0, v_a_5562_);
                    lean_closure_set(v___f_5565_, 1, v_elimExpr_5553_);
                    lean_closure_set(v___f_5565_, 2, v_baseDeclName_x3f_5554_);
                    if v_hasTrace_5564_ == 0 {
                        lean_dec_ref(v_elimExpr_5553_);
                        v___y_5567_ = v_a_5555_;
                        v___y_5568_ = v_a_5556_;
                        v___y_5569_ = v_a_5557_;
                        v___y_5570_ = v_a_5558_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5573_ = l_Lean_Meta_getElimExprInfo___closed__2;
                        v___x_5574_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___closed__5_once),
                            _init_l_Lean_Meta_getElimExprInfo___closed__5,
                        );
                        v___x_5575_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5563_,
                            v_options_5561_,
                            v___x_5574_,
                        );
                        if v___x_5575_ == 0 {
                            lean_dec_ref(v_elimExpr_5553_);
                            v___y_5567_ = v_a_5555_;
                            v___y_5568_ = v_a_5556_;
                            v___y_5569_ = v_a_5557_;
                            v___y_5570_ = v_a_5558_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5576_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___closed__7),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getElimExprInfo___closed__7_once
                                ),
                                _init_l_Lean_Meta_getElimExprInfo___closed__7,
                            );
                            v___x_5577_ = l_Lean_indentExpr(v_elimExpr_5553_);
                            v___x_5578_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5578_, 0, v___x_5576_);
                            lean_ctor_set(v___x_5578_, 1, v___x_5577_);
                            v___x_5579_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_getElimExprInfo___closed__9),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getElimExprInfo___closed__9_once
                                ),
                                _init_l_Lean_Meta_getElimExprInfo___closed__9,
                            );
                            v___x_5580_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5580_, 0, v___x_5578_);
                            lean_ctor_set(v___x_5580_, 1, v___x_5579_);
                            lean_inc(v_a_5562_);
                            v___x_5581_ = l_Lean_indentExpr(v_a_5562_);
                            v___x_5582_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5582_, 0, v___x_5580_);
                            lean_ctor_set(v___x_5582_, 1, v___x_5581_);
                            v___x_5583_ =
                                l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(
                                    v___x_5573_,
                                    v___x_5582_,
                                    v_a_5555_,
                                    v_a_5556_,
                                    v_a_5557_,
                                    v_a_5558_,
                                );
                            if lean_obj_tag(v___x_5583_) == 0 {
                                lean_dec_ref_known(v___x_5583_, 1);
                                v___y_5567_ = v_a_5555_;
                                v___y_5568_ = v_a_5556_;
                                v___y_5569_ = v_a_5557_;
                                v___y_5570_ = v_a_5558_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___f_5565_);
                                lean_dec(v_a_5562_);
                                v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
                                v_isSharedCheck_5591_ = (!lean_is_exclusive(v___x_5583_)) as u8;
                                if v_isSharedCheck_5591_ == 0 {
                                    v___x_5586_ = v___x_5583_;
                                    v_isShared_5587_ = v_isSharedCheck_5591_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5584_);
                                    lean_dec(v___x_5583_);
                                    v___x_5586_ = lean_box(0);
                                    v_isShared_5587_ = v_isSharedCheck_5591_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_baseDeclName_x3f_5554_);
                    lean_dec_ref(v_elimExpr_5553_);
                    v_a_5592_ = lean_ctor_get(v___x_5560_, 0);
                    v_isSharedCheck_5599_ = (!lean_is_exclusive(v___x_5560_)) as u8;
                    if v_isSharedCheck_5599_ == 0 {
                        v___x_5594_ = v___x_5560_;
                        v_isShared_5595_ = v_isSharedCheck_5599_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5592_);
                        lean_dec(v___x_5560_);
                        v___x_5594_ = lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5599_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5571_ = 0;
                v___x_5572_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_5562_, v___f_5565_, v___x_5571_, v___x_5571_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
                return v___x_5572_;
            }
            2 => {
                if v_isShared_5587_ == 0 {
                    v___x_5589_ = v___x_5586_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5589_;
            }
            4 => {
                if v_isShared_5595_ == 0 {
                    v___x_5597_ = v___x_5594_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
                    v___x_5597_ = v_reuseFailAlloc_5598_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getElimExprInfo___boxed(
    mut v_elimExpr_5600_: *mut LeanObject,
    mut v_baseDeclName_x3f_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
    mut v_a_5603_: *mut LeanObject,
    mut v_a_5604_: *mut LeanObject,
    mut v_a_5605_: *mut LeanObject,
    mut v_a_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5607_: *mut LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lean_Meta_getElimExprInfo(
        v_elimExpr_5600_,
        v_baseDeclName_x3f_5601_,
        v_a_5602_,
        v_a_5603_,
        v_a_5604_,
        v_a_5605_,
    );
    lean_dec(v_a_5605_);
    lean_dec_ref(v_a_5604_);
    lean_dec(v_a_5603_);
    lean_dec_ref(v_a_5602_);
    return v_res_5607_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(
    mut v_00_u03b1_5608_: *mut LeanObject,
    mut v_msg_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    v___x_5615_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
        v_msg_5609_,
        v___y_5610_,
        v___y_5611_,
        v___y_5612_,
        v___y_5613_,
    );
    return v___x_5615_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(
    mut v_00_u03b1_5616_: *mut LeanObject,
    mut v_msg_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5623_: *mut LeanObject = core::ptr::null_mut();
    v_res_5623_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(
        v_00_u03b1_5616_,
        v_msg_5617_,
        v___y_5618_,
        v___y_5619_,
        v___y_5620_,
        v___y_5621_,
    );
    lean_dec(v___y_5621_);
    lean_dec_ref(v___y_5620_);
    lean_dec(v___y_5619_);
    lean_dec_ref(v___y_5618_);
    return v_res_5623_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(
    mut v_upperBound_5624_: *mut LeanObject,
    mut v_xs_5625_: *mut LeanObject,
    mut v_motive_5626_: *mut LeanObject,
    mut v___x_5627_: *mut LeanObject,
    mut v_baseDeclName_x3f_5628_: *mut LeanObject,
    mut v___x_5629_: *mut LeanObject,
    mut v_inst_5630_: *mut LeanObject,
    mut v_R_5631_: *mut LeanObject,
    mut v_a_5632_: *mut LeanObject,
    mut v_b_5633_: *mut LeanObject,
    mut v_c_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    v___x_5640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(
        v_upperBound_5624_,
        v_xs_5625_,
        v_motive_5626_,
        v___x_5627_,
        v_baseDeclName_x3f_5628_,
        v___x_5629_,
        v_a_5632_,
        v_b_5633_,
        v___y_5635_,
        v___y_5637_,
        v___y_5638_,
    );
    return v___x_5640_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(
    mut v_upperBound_5641_: *mut LeanObject,
    mut v_xs_5642_: *mut LeanObject,
    mut v_motive_5643_: *mut LeanObject,
    mut v___x_5644_: *mut LeanObject,
    mut v_baseDeclName_x3f_5645_: *mut LeanObject,
    mut v___x_5646_: *mut LeanObject,
    mut v_inst_5647_: *mut LeanObject,
    mut v_R_5648_: *mut LeanObject,
    mut v_a_5649_: *mut LeanObject,
    mut v_b_5650_: *mut LeanObject,
    mut v_c_5651_: *mut LeanObject,
    mut v___y_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5657_: *mut LeanObject = core::ptr::null_mut();
    v_res_5657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(
        v_upperBound_5641_,
        v_xs_5642_,
        v_motive_5643_,
        v___x_5644_,
        v_baseDeclName_x3f_5645_,
        v___x_5646_,
        v_inst_5647_,
        v_R_5648_,
        v_a_5649_,
        v_b_5650_,
        v_c_5651_,
        v___y_5652_,
        v___y_5653_,
        v___y_5654_,
        v___y_5655_,
    );
    lean_dec(v___y_5655_);
    lean_dec_ref(v___y_5654_);
    lean_dec(v___y_5653_);
    lean_dec_ref(v___y_5652_);
    lean_dec_ref(v___x_5644_);
    lean_dec_ref(v_motive_5643_);
    lean_dec_ref(v_xs_5642_);
    lean_dec(v_upperBound_5641_);
    return v_res_5657_;
}
pub unsafe fn l_Lean_Meta_getElimInfo(
    mut v_elimName_5658_: *mut LeanObject,
    mut v_baseDeclName_x3f_5659_: *mut LeanObject,
    mut v_a_5660_: *mut LeanObject,
    mut v_a_5661_: *mut LeanObject,
    mut v_a_5662_: *mut LeanObject,
    mut v_a_5663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5665_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v_elimName_5658_,
                    v_a_5660_,
                    v_a_5661_,
                    v_a_5662_,
                    v_a_5663_,
                );
                if lean_obj_tag(v___x_5665_) == 0 {
                    v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
                    lean_inc(v_a_5666_);
                    lean_dec_ref_known(v___x_5665_, 1);
                    v___x_5667_ = l_Lean_Meta_getElimExprInfo(
                        v_a_5666_,
                        v_baseDeclName_x3f_5659_,
                        v_a_5660_,
                        v_a_5661_,
                        v_a_5662_,
                        v_a_5663_,
                    );
                    return v___x_5667_;
                } else {
                    lean_dec(v_baseDeclName_x3f_5659_);
                    v_a_5668_ = lean_ctor_get(v___x_5665_, 0);
                    v_isSharedCheck_5675_ = (!lean_is_exclusive(v___x_5665_)) as u8;
                    if v_isSharedCheck_5675_ == 0 {
                        v___x_5670_ = v___x_5665_;
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5668_);
                        lean_dec(v___x_5665_);
                        v___x_5670_ = lean_box(0);
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5671_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getElimInfo___boxed(
    mut v_elimName_5676_: *mut LeanObject,
    mut v_baseDeclName_x3f_5677_: *mut LeanObject,
    mut v_a_5678_: *mut LeanObject,
    mut v_a_5679_: *mut LeanObject,
    mut v_a_5680_: *mut LeanObject,
    mut v_a_5681_: *mut LeanObject,
    mut v_a_5682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5683_: *mut LeanObject = core::ptr::null_mut();
    v_res_5683_ = l_Lean_Meta_getElimInfo(
        v_elimName_5676_,
        v_baseDeclName_x3f_5677_,
        v_a_5678_,
        v_a_5679_,
        v_a_5680_,
        v_a_5681_,
    );
    lean_dec(v_a_5681_);
    lean_dec_ref(v_a_5680_);
    lean_dec(v_a_5679_);
    lean_dec_ref(v_a_5678_);
    return v_res_5683_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(
    mut v_a_5684_: *mut LeanObject,
    mut v_as_5685_: *mut LeanObject,
    mut v_i_5686_: usize,
    mut v_stop_5687_: usize,
) -> u8 {
    let mut v___x_5688_: u8 = 0;
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5691_: usize = 0;
    let mut v___x_5692_: usize = 0;
    let mut v___x_5694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5688_ = lean_usize_dec_eq(v_i_5686_, v_stop_5687_);
                if v___x_5688_ == 0 {
                    v___x_5689_ = lean_array_uget_borrowed(v_as_5685_, v_i_5686_);
                    v___x_5690_ = lean_nat_dec_eq(v_a_5684_, v___x_5689_);
                    if v___x_5690_ == 0 {
                        v___x_5691_ = 1usize;
                        v___x_5692_ = lean_usize_add(v_i_5686_, v___x_5691_);
                        v_i_5686_ = v___x_5692_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5690_;
                    }
                } else {
                    v___x_5694_ = 0;
                    return v___x_5694_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(
    mut v_a_5695_: *mut LeanObject,
    mut v_as_5696_: *mut LeanObject,
    mut v_i_5697_: *mut LeanObject,
    mut v_stop_5698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5699_: usize = 0;
    let mut v_stop_boxed_5700_: usize = 0;
    let mut v_res_5701_: u8 = 0;
    let mut v_r_5702_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5699_ = lean_unbox_usize(v_i_5697_);
    lean_dec(v_i_5697_);
    v_stop_boxed_5700_ = lean_unbox_usize(v_stop_5698_);
    lean_dec(v_stop_5698_);
    v_res_5701_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_5695_, v_as_5696_, v_i_boxed_5699_, v_stop_boxed_5700_);
    lean_dec_ref(v_as_5696_);
    lean_dec(v_a_5695_);
    v_r_5702_ = lean_box((v_res_5701_) as usize);
    return v_r_5702_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(
    mut v_as_5703_: *mut LeanObject,
    mut v_a_5704_: *mut LeanObject,
) -> u8 {
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: u8 = 0;
    v___x_5705_ = lean_unsigned_to_nat(0);
    v___x_5706_ = lean_array_get_size(v_as_5703_);
    v___x_5707_ = lean_nat_dec_lt(v___x_5705_, v___x_5706_);
    if v___x_5707_ == 0 {
        return v___x_5707_;
    } else {
        if v___x_5707_ == 0 {
            return v___x_5707_;
        } else {
            let mut v___x_5708_: usize = 0;
            let mut v___x_5709_: usize = 0;
            let mut v___x_5710_: u8 = 0;
            v___x_5708_ = 0usize;
            v___x_5709_ = lean_usize_of_nat(v___x_5706_);
            v___x_5710_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_5704_, v_as_5703_, v___x_5708_, v___x_5709_);
            return v___x_5710_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(
    mut v_as_5711_: *mut LeanObject,
    mut v_a_5712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5713_: u8 = 0;
    let mut v_r_5714_: *mut LeanObject = core::ptr::null_mut();
    v_res_5713_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_5711_, v_a_5712_);
    lean_dec(v_a_5712_);
    lean_dec_ref(v_as_5711_);
    v_r_5714_ = lean_box((v_res_5713_) as usize);
    return v_r_5714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2()
-> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ =
        l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1;
    v___x_5719_ = l_Lean_stringToMessageData(v___x_5718_);
    return v___x_5719_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4()
-> *mut LeanObject {
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    v___x_5721_ =
        l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3;
    v___x_5722_ = l_Lean_stringToMessageData(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6()
-> *mut LeanObject {
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    v___x_5724_ =
        l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5;
    v___x_5725_ = l_Lean_stringToMessageData(v___x_5724_);
    return v___x_5725_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8()
-> *mut LeanObject {
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    v___x_5727_ =
        l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7;
    v___x_5728_ = l_Lean_stringToMessageData(v___x_5727_);
    return v___x_5728_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10()
-> *mut LeanObject {
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    v___x_5730_ =
        l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9;
    v___x_5731_ = l_Lean_stringToMessageData(v___x_5730_);
    return v___x_5731_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(
    mut v_elimInfo_5732_: *mut LeanObject,
    mut v_targets_5733_: *mut LeanObject,
    mut v_type_5734_: *mut LeanObject,
    mut v_argIdx_5735_: *mut LeanObject,
    mut v_targetIdx_5736_: *mut LeanObject,
    mut v_implicits_5737_: *mut LeanObject,
    mut v_targets_x27_5738_: *mut LeanObject,
    mut v_a_5739_: *mut LeanObject,
    mut v_a_5740_: *mut LeanObject,
    mut v_a_5741_: *mut LeanObject,
    mut v_a_5742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5752_: u8 = 0;
    let mut v___y_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5791_: u8 = 0;
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v_a_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut v_a_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5807_: u8 = 0;
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5811_: u8 = 0;
    let mut v_a_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5815_: u8 = 0;
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5819_: u8 = 0;
    let mut v_elimExpr_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetsPos_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: u8 = 0;
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5839_: u8 = 0;
    let mut v___x_5840_: u8 = 0;
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: u8 = 0;
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5855_: u8 = 0;
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: u8 = 0;
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5871_: u8 = 0;
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: u8 = 0;
    let mut v_elimExpr_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5892_: u8 = 0;
    let mut v_a_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5896_: u8 = 0;
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5747_ =
                    l_Lean_Meta_whnfD(v_type_5734_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
                if lean_obj_tag(v___x_5747_) == 0 {
                    v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
                    lean_inc(v_a_5748_);
                    lean_dec_ref_known(v___x_5747_, 1);
                    if lean_obj_tag(v_a_5748_) == 7 {
                        v_binderName_5749_ = lean_ctor_get(v_a_5748_, 0);
                        lean_inc(v_binderName_5749_);
                        v_binderType_5750_ = lean_ctor_get(v_a_5748_, 1);
                        lean_inc_ref(v_binderType_5750_);
                        v_body_5751_ = lean_ctor_get(v_a_5748_, 2);
                        lean_inc_ref(v_body_5751_);
                        v_binderInfo_5752_ = lean_ctor_get_uint8(
                            v_a_5748_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_dec_ref_known(v_a_5748_, 3);
                        v_elimExpr_5820_ = lean_ctor_get(v_elimInfo_5732_, 0);
                        v_targetsPos_5821_ = lean_ctor_get(v_elimInfo_5732_, 3);
                        v___x_5822_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_5821_, v_argIdx_5735_);
                        if v___x_5822_ == 0 {
                            lean_dec(v_binderName_5749_);
                            v___x_5823_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5823_, 0, v_binderType_5750_);
                            v___x_5824_ = 0;
                            v___x_5825_ = lean_box(0);
                            v___x_5826_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_5823_,
                                v___x_5824_,
                                v___x_5825_,
                                v_a_5739_,
                                v_a_5740_,
                                v_a_5741_,
                                v_a_5742_,
                            );
                            if lean_obj_tag(v___x_5826_) == 0 {
                                v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
                                lean_inc(v_a_5827_);
                                lean_dec_ref_known(v___x_5826_, 1);
                                v___x_5828_ = lean_expr_instantiate1(v_body_5751_, v_a_5827_);
                                lean_dec(v_a_5827_);
                                lean_dec_ref(v_body_5751_);
                                v___x_5829_ = lean_unsigned_to_nat(1);
                                v___x_5830_ = lean_nat_add(v_argIdx_5735_, v___x_5829_);
                                lean_dec(v_argIdx_5735_);
                                v_type_5734_ = v___x_5828_;
                                v_argIdx_5735_ = v___x_5830_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_body_5751_);
                                lean_dec_ref(v_targets_x27_5738_);
                                lean_dec_ref(v_implicits_5737_);
                                lean_dec(v_targetIdx_5736_);
                                lean_dec(v_argIdx_5735_);
                                lean_dec_ref(v_elimInfo_5732_);
                                v_a_5832_ = lean_ctor_get(v___x_5826_, 0);
                                v_isSharedCheck_5839_ = (!lean_is_exclusive(v___x_5826_)) as u8;
                                if v_isSharedCheck_5839_ == 0 {
                                    v___x_5834_ = v___x_5826_;
                                    v_isShared_5835_ = v_isSharedCheck_5839_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_5832_);
                                    lean_dec(v___x_5826_);
                                    v___x_5834_ = lean_box(0);
                                    v_isShared_5835_ = v_isSharedCheck_5839_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            v___x_5840_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_5752_);
                            if v___x_5840_ == 0 {
                                v___x_5841_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_5841_, 0, v_binderType_5750_);
                                v___x_5842_ = 0;
                                v___x_5843_ = l_Lean_Meta_mkFreshExprMVar(
                                    v___x_5841_,
                                    v___x_5842_,
                                    v_binderName_5749_,
                                    v_a_5739_,
                                    v_a_5740_,
                                    v_a_5741_,
                                    v_a_5742_,
                                );
                                if lean_obj_tag(v___x_5843_) == 0 {
                                    v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
                                    lean_inc(v_a_5844_);
                                    lean_dec_ref_known(v___x_5843_, 1);
                                    v___x_5845_ = lean_expr_instantiate1(v_body_5751_, v_a_5844_);
                                    lean_dec_ref(v_body_5751_);
                                    v___x_5846_ = lean_unsigned_to_nat(1);
                                    v___x_5847_ = lean_nat_add(v_argIdx_5735_, v___x_5846_);
                                    lean_dec(v_argIdx_5735_);
                                    v___x_5848_ = l_Lean_Expr_mvarId_x21(v_a_5844_);
                                    v___x_5849_ = lean_array_push(v_implicits_5737_, v___x_5848_);
                                    v___x_5850_ = lean_array_push(v_targets_x27_5738_, v_a_5844_);
                                    v_type_5734_ = v___x_5845_;
                                    v_argIdx_5735_ = v___x_5847_;
                                    v_implicits_5737_ = v___x_5849_;
                                    v_targets_x27_5738_ = v___x_5850_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_body_5751_);
                                    lean_dec_ref(v_targets_x27_5738_);
                                    lean_dec_ref(v_implicits_5737_);
                                    lean_dec(v_targetIdx_5736_);
                                    lean_dec(v_argIdx_5735_);
                                    lean_dec_ref(v_elimInfo_5732_);
                                    v_a_5852_ = lean_ctor_get(v___x_5843_, 0);
                                    v_isSharedCheck_5859_ = (!lean_is_exclusive(v___x_5843_)) as u8;
                                    if v_isSharedCheck_5859_ == 0 {
                                        v___x_5854_ = v___x_5843_;
                                        v_isShared_5855_ = v_isSharedCheck_5859_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5852_);
                                        lean_dec(v___x_5843_);
                                        v___x_5854_ = lean_box(0);
                                        v_isShared_5855_ = v_isSharedCheck_5859_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_binderName_5749_);
                                v___x_5860_ = lean_array_get_size(v_targets_5733_);
                                v___x_5861_ = lean_nat_dec_lt(v_targetIdx_5736_, v___x_5860_);
                                if v___x_5861_ == 0 {
                                    v___x_5862_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
                                    lean_inc_ref(v_elimExpr_5820_);
                                    v___x_5863_ = l_Lean_MessageData_ofExpr(v_elimExpr_5820_);
                                    v___x_5864_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5864_, 0, v___x_5862_);
                                    lean_ctor_set(v___x_5864_, 1, v___x_5863_);
                                    v___x_5865_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
                                    v___x_5866_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5866_, 0, v___x_5864_);
                                    lean_ctor_set(v___x_5866_, 1, v___x_5865_);
                                    v___x_5867_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_5866_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
                                    if lean_obj_tag(v___x_5867_) == 0 {
                                        lean_dec_ref_known(v___x_5867_, 1);
                                        v___y_5766_ = v_a_5739_;
                                        v___y_5767_ = v_a_5740_;
                                        v___y_5768_ = v_a_5741_;
                                        v___y_5769_ = v_a_5742_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_body_5751_);
                                        lean_dec_ref(v_binderType_5750_);
                                        lean_dec_ref(v_targets_x27_5738_);
                                        lean_dec_ref(v_implicits_5737_);
                                        lean_dec(v_targetIdx_5736_);
                                        lean_dec(v_argIdx_5735_);
                                        lean_dec_ref(v_elimInfo_5732_);
                                        v_a_5868_ = lean_ctor_get(v___x_5867_, 0);
                                        v_isSharedCheck_5875_ =
                                            (!lean_is_exclusive(v___x_5867_)) as u8;
                                        if v_isSharedCheck_5875_ == 0 {
                                            v___x_5870_ = v___x_5867_;
                                            v_isShared_5871_ = v_isSharedCheck_5875_;
                                            state = 16;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5868_);
                                            lean_dec(v___x_5867_);
                                            v___x_5870_ = lean_box(0);
                                            v_isShared_5871_ = v_isSharedCheck_5875_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___y_5766_ = v_a_5739_;
                                    v___y_5767_ = v_a_5740_;
                                    v___y_5768_ = v_a_5741_;
                                    v___y_5769_ = v_a_5742_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_5748_);
                        lean_dec(v_argIdx_5735_);
                        v___x_5876_ = lean_array_get_size(v_targets_5733_);
                        v___x_5877_ = lean_nat_dec_eq(v_targetIdx_5736_, v___x_5876_);
                        lean_dec(v_targetIdx_5736_);
                        if v___x_5877_ == 0 {
                            v_elimExpr_5878_ = lean_ctor_get(v_elimInfo_5732_, 0);
                            lean_inc_ref(v_elimExpr_5878_);
                            lean_dec_ref(v_elimInfo_5732_);
                            v___x_5879_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
                            v___x_5880_ = l_Lean_MessageData_ofExpr(v_elimExpr_5878_);
                            v___x_5881_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5881_, 0, v___x_5879_);
                            lean_ctor_set(v___x_5881_, 1, v___x_5880_);
                            v___x_5882_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
                            v___x_5883_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5883_, 0, v___x_5881_);
                            lean_ctor_set(v___x_5883_, 1, v___x_5882_);
                            v___x_5884_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_5883_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
                            if lean_obj_tag(v___x_5884_) == 0 {
                                lean_dec_ref_known(v___x_5884_, 1);
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_targets_x27_5738_);
                                lean_dec_ref(v_implicits_5737_);
                                v_a_5885_ = lean_ctor_get(v___x_5884_, 0);
                                v_isSharedCheck_5892_ = (!lean_is_exclusive(v___x_5884_)) as u8;
                                if v_isSharedCheck_5892_ == 0 {
                                    v___x_5887_ = v___x_5884_;
                                    v_isShared_5888_ = v_isSharedCheck_5892_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_5885_);
                                    lean_dec(v___x_5884_);
                                    v___x_5887_ = lean_box(0);
                                    v_isShared_5888_ = v_isSharedCheck_5892_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_elimInfo_5732_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_targets_x27_5738_);
                    lean_dec_ref(v_implicits_5737_);
                    lean_dec(v_targetIdx_5736_);
                    lean_dec(v_argIdx_5735_);
                    lean_dec_ref(v_elimInfo_5732_);
                    v_a_5893_ = lean_ctor_get(v___x_5747_, 0);
                    v_isSharedCheck_5900_ = (!lean_is_exclusive(v___x_5747_)) as u8;
                    if v_isSharedCheck_5900_ == 0 {
                        v___x_5895_ = v___x_5747_;
                        v_isShared_5896_ = v_isSharedCheck_5900_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_5893_);
                        lean_dec(v___x_5747_);
                        v___x_5895_ = lean_box(0);
                        v_isShared_5896_ = v_isSharedCheck_5900_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5745_, 0, v_implicits_5737_);
                lean_ctor_set(v___x_5745_, 1, v_targets_x27_5738_);
                v___x_5746_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5746_, 0, v___x_5745_);
                return v___x_5746_;
            }
            2 => {
                v___x_5759_ = lean_expr_instantiate1(v_body_5751_, v___y_5754_);
                lean_dec_ref(v_body_5751_);
                v___x_5760_ = lean_unsigned_to_nat(1);
                v___x_5761_ = lean_nat_add(v_argIdx_5735_, v___x_5760_);
                lean_dec(v_argIdx_5735_);
                v___x_5762_ = lean_nat_add(v_targetIdx_5736_, v___x_5760_);
                lean_dec(v_targetIdx_5736_);
                v___x_5763_ = lean_array_push(v_targets_x27_5738_, v___y_5754_);
                v_type_5734_ = v___x_5759_;
                v_argIdx_5735_ = v___x_5761_;
                v_targetIdx_5736_ = v___x_5762_;
                v_targets_x27_5738_ = v___x_5763_;
                v_a_5739_ = v___y_5755_;
                v_a_5740_ = v___y_5756_;
                v_a_5741_ = v___y_5757_;
                v_a_5742_ = v___y_5758_;
                state = 0;
                continue;
            }
            3 => {
                v___x_5770_ = l_Lean_instInhabitedExpr;
                v___x_5771_ =
                    lean_array_get_borrowed(v___x_5770_, v_targets_5733_, v_targetIdx_5736_);
                lean_inc(v___y_5769_);
                lean_inc_ref(v___y_5768_);
                lean_inc(v___y_5767_);
                lean_inc_ref(v___y_5766_);
                lean_inc(v___x_5771_);
                v___x_5772_ = lean_infer_type(
                    v___x_5771_,
                    v___y_5766_,
                    v___y_5767_,
                    v___y_5768_,
                    v___y_5769_,
                );
                if lean_obj_tag(v___x_5772_) == 0 {
                    v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
                    lean_inc_n(v_a_5773_, 2);
                    lean_dec_ref_known(v___x_5772_, 1);
                    lean_inc_ref(v_binderType_5750_);
                    v___x_5774_ = l_Lean_Meta_isExprDefEq(
                        v_binderType_5750_,
                        v_a_5773_,
                        v___y_5766_,
                        v___y_5767_,
                        v___y_5768_,
                        v___y_5769_,
                    );
                    if lean_obj_tag(v___x_5774_) == 0 {
                        v_a_5775_ = lean_ctor_get(v___x_5774_, 0);
                        lean_inc(v_a_5775_);
                        lean_dec_ref_known(v___x_5774_, 1);
                        v___x_5776_ = (lean_unbox(v_a_5775_) as u8);
                        lean_dec(v_a_5775_);
                        if v___x_5776_ == 0 {
                            v___x_5777_ = lean_box(0);
                            v___x_5778_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0;
                            v___x_5779_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(
                                v_a_5773_,
                                v_binderType_5750_,
                                v___x_5777_,
                                v___x_5778_,
                            );
                            if lean_obj_tag(v___x_5779_) == 0 {
                                v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
                                lean_inc(v_a_5780_);
                                lean_dec_ref_known(v___x_5779_, 1);
                                v___x_5781_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
                                lean_inc(v___x_5771_);
                                v___x_5782_ = l_Lean_indentExpr(v___x_5771_);
                                v___x_5783_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5783_, 0, v___x_5781_);
                                lean_ctor_set(v___x_5783_, 1, v___x_5782_);
                                v___x_5784_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
                                v___x_5785_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5785_, 0, v___x_5783_);
                                lean_ctor_set(v___x_5785_, 1, v___x_5784_);
                                v___x_5786_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5786_, 0, v___x_5785_);
                                lean_ctor_set(v___x_5786_, 1, v_a_5780_);
                                v___x_5787_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_5786_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
                                if lean_obj_tag(v___x_5787_) == 0 {
                                    lean_dec_ref_known(v___x_5787_, 1);
                                    lean_inc(v___x_5771_);
                                    v___y_5754_ = v___x_5771_;
                                    v___y_5755_ = v___y_5766_;
                                    v___y_5756_ = v___y_5767_;
                                    v___y_5757_ = v___y_5768_;
                                    v___y_5758_ = v___y_5769_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec_ref(v_body_5751_);
                                    lean_dec_ref(v_targets_x27_5738_);
                                    lean_dec_ref(v_implicits_5737_);
                                    lean_dec(v_targetIdx_5736_);
                                    lean_dec(v_argIdx_5735_);
                                    lean_dec_ref(v_elimInfo_5732_);
                                    v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
                                    v_isSharedCheck_5795_ = (!lean_is_exclusive(v___x_5787_)) as u8;
                                    if v_isSharedCheck_5795_ == 0 {
                                        v___x_5790_ = v___x_5787_;
                                        v_isShared_5791_ = v_isSharedCheck_5795_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5788_);
                                        lean_dec(v___x_5787_);
                                        v___x_5790_ = lean_box(0);
                                        v_isShared_5791_ = v_isSharedCheck_5795_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_body_5751_);
                                lean_dec_ref(v_targets_x27_5738_);
                                lean_dec_ref(v_implicits_5737_);
                                lean_dec(v_targetIdx_5736_);
                                lean_dec(v_argIdx_5735_);
                                lean_dec_ref(v_elimInfo_5732_);
                                v_a_5796_ = lean_ctor_get(v___x_5779_, 0);
                                v_isSharedCheck_5803_ = (!lean_is_exclusive(v___x_5779_)) as u8;
                                if v_isSharedCheck_5803_ == 0 {
                                    v___x_5798_ = v___x_5779_;
                                    v_isShared_5799_ = v_isSharedCheck_5803_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5796_);
                                    lean_dec(v___x_5779_);
                                    v___x_5798_ = lean_box(0);
                                    v_isShared_5799_ = v_isSharedCheck_5803_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5773_);
                            lean_dec_ref(v_binderType_5750_);
                            lean_inc(v___x_5771_);
                            v___y_5754_ = v___x_5771_;
                            v___y_5755_ = v___y_5766_;
                            v___y_5756_ = v___y_5767_;
                            v___y_5757_ = v___y_5768_;
                            v___y_5758_ = v___y_5769_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5773_);
                        lean_dec_ref(v_body_5751_);
                        lean_dec_ref(v_binderType_5750_);
                        lean_dec_ref(v_targets_x27_5738_);
                        lean_dec_ref(v_implicits_5737_);
                        lean_dec(v_targetIdx_5736_);
                        lean_dec(v_argIdx_5735_);
                        lean_dec_ref(v_elimInfo_5732_);
                        v_a_5804_ = lean_ctor_get(v___x_5774_, 0);
                        v_isSharedCheck_5811_ = (!lean_is_exclusive(v___x_5774_)) as u8;
                        if v_isSharedCheck_5811_ == 0 {
                            v___x_5806_ = v___x_5774_;
                            v_isShared_5807_ = v_isSharedCheck_5811_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5804_);
                            lean_dec(v___x_5774_);
                            v___x_5806_ = lean_box(0);
                            v_isShared_5807_ = v_isSharedCheck_5811_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_body_5751_);
                    lean_dec_ref(v_binderType_5750_);
                    lean_dec_ref(v_targets_x27_5738_);
                    lean_dec_ref(v_implicits_5737_);
                    lean_dec(v_targetIdx_5736_);
                    lean_dec(v_argIdx_5735_);
                    lean_dec_ref(v_elimInfo_5732_);
                    v_a_5812_ = lean_ctor_get(v___x_5772_, 0);
                    v_isSharedCheck_5819_ = (!lean_is_exclusive(v___x_5772_)) as u8;
                    if v_isSharedCheck_5819_ == 0 {
                        v___x_5814_ = v___x_5772_;
                        v_isShared_5815_ = v_isSharedCheck_5819_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5812_);
                        lean_dec(v___x_5772_);
                        v___x_5814_ = lean_box(0);
                        v_isShared_5815_ = v_isSharedCheck_5819_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5791_ == 0 {
                    v___x_5793_ = v___x_5790_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_a_5788_);
                    v___x_5793_ = v_reuseFailAlloc_5794_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5793_;
            }
            6 => {
                if v_isShared_5799_ == 0 {
                    v___x_5801_ = v___x_5798_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5796_);
                    v___x_5801_ = v_reuseFailAlloc_5802_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5801_;
            }
            8 => {
                if v_isShared_5807_ == 0 {
                    v___x_5809_ = v___x_5806_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5810_, 0, v_a_5804_);
                    v___x_5809_ = v_reuseFailAlloc_5810_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5809_;
            }
            10 => {
                if v_isShared_5815_ == 0 {
                    v___x_5817_ = v___x_5814_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_a_5812_);
                    v___x_5817_ = v_reuseFailAlloc_5818_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5817_;
            }
            12 => {
                if v_isShared_5835_ == 0 {
                    v___x_5837_ = v___x_5834_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5838_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_a_5832_);
                    v___x_5837_ = v_reuseFailAlloc_5838_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5837_;
            }
            14 => {
                if v_isShared_5855_ == 0 {
                    v___x_5857_ = v___x_5854_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
                    v___x_5857_ = v_reuseFailAlloc_5858_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5857_;
            }
            16 => {
                if v_isShared_5871_ == 0 {
                    v___x_5873_ = v___x_5870_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5868_);
                    v___x_5873_ = v_reuseFailAlloc_5874_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5873_;
            }
            18 => {
                if v_isShared_5888_ == 0 {
                    v___x_5890_ = v___x_5887_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_a_5885_);
                    v___x_5890_ = v_reuseFailAlloc_5891_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5890_;
            }
            20 => {
                if v_isShared_5896_ == 0 {
                    v___x_5898_ = v___x_5895_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_a_5893_);
                    v___x_5898_ = v_reuseFailAlloc_5899_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(
    mut v_elimInfo_5901_: *mut LeanObject,
    mut v_targets_5902_: *mut LeanObject,
    mut v_type_5903_: *mut LeanObject,
    mut v_argIdx_5904_: *mut LeanObject,
    mut v_targetIdx_5905_: *mut LeanObject,
    mut v_implicits_5906_: *mut LeanObject,
    mut v_targets_x27_5907_: *mut LeanObject,
    mut v_a_5908_: *mut LeanObject,
    mut v_a_5909_: *mut LeanObject,
    mut v_a_5910_: *mut LeanObject,
    mut v_a_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5913_: *mut LeanObject = core::ptr::null_mut();
    v_res_5913_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(
        v_elimInfo_5901_,
        v_targets_5902_,
        v_type_5903_,
        v_argIdx_5904_,
        v_targetIdx_5905_,
        v_implicits_5906_,
        v_targets_x27_5907_,
        v_a_5908_,
        v_a_5909_,
        v_a_5910_,
        v_a_5911_,
    );
    lean_dec(v_a_5911_);
    lean_dec_ref(v_a_5910_);
    lean_dec(v_a_5909_);
    lean_dec_ref(v_a_5908_);
    lean_dec_ref(v_targets_5902_);
    return v_res_5913_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(
    mut v_e_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5917_: u8 = 0;
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_unused_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5917_ = l_Lean_Expr_hasMVar(v_e_5914_);
                if v___x_5917_ == 0 {
                    v___x_5918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5918_, 0, v_e_5914_);
                    return v___x_5918_;
                } else {
                    v___x_5919_ = lean_st_ref_get(v___y_5915_);
                    v_mctx_5920_ = lean_ctor_get(v___x_5919_, 0);
                    lean_inc_ref(v_mctx_5920_);
                    lean_dec(v___x_5919_);
                    v___x_5921_ = l_Lean_instantiateMVarsCore(v_mctx_5920_, v_e_5914_);
                    v_fst_5922_ = lean_ctor_get(v___x_5921_, 0);
                    lean_inc(v_fst_5922_);
                    v_snd_5923_ = lean_ctor_get(v___x_5921_, 1);
                    lean_inc(v_snd_5923_);
                    lean_dec_ref(v___x_5921_);
                    v___x_5924_ = lean_st_ref_take(v___y_5915_);
                    v_cache_5925_ = lean_ctor_get(v___x_5924_, 1);
                    v_zetaDeltaFVarIds_5926_ = lean_ctor_get(v___x_5924_, 2);
                    v_postponed_5927_ = lean_ctor_get(v___x_5924_, 3);
                    v_diag_5928_ = lean_ctor_get(v___x_5924_, 4);
                    v_isSharedCheck_5937_ = (!lean_is_exclusive(v___x_5924_)) as u8;
                    if v_isSharedCheck_5937_ == 0 {
                        v_unused_5938_ = lean_ctor_get(v___x_5924_, 0);
                        lean_dec(v_unused_5938_);
                        v___x_5930_ = v___x_5924_;
                        v_isShared_5931_ = v_isSharedCheck_5937_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5928_);
                        lean_inc(v_postponed_5927_);
                        lean_inc(v_zetaDeltaFVarIds_5926_);
                        lean_inc(v_cache_5925_);
                        lean_dec(v___x_5924_);
                        v___x_5930_ = lean_box(0);
                        v_isShared_5931_ = v_isSharedCheck_5937_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5931_ == 0 {
                    lean_ctor_set(v___x_5930_, 0, v_snd_5923_);
                    v___x_5933_ = v___x_5930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_snd_5923_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_cache_5925_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 2, v_zetaDeltaFVarIds_5926_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 3, v_postponed_5927_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 4, v_diag_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5934_ = lean_st_ref_set(v___y_5915_, v___x_5933_);
                v___x_5935_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5935_, 0, v_fst_5922_);
                return v___x_5935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(
    mut v_e_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5942_: *mut LeanObject = core::ptr::null_mut();
    v_res_5942_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(
        v_e_5939_,
        v___y_5940_,
    );
    lean_dec(v___y_5940_);
    return v_res_5942_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(
    mut v_e_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    v___x_5949_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(
        v_e_5943_,
        v___y_5945_,
    );
    return v___x_5949_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(
    mut v_e_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
    mut v___y_5952_: *mut LeanObject,
    mut v___y_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5956_: *mut LeanObject = core::ptr::null_mut();
    v_res_5956_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(
        v_e_5950_,
        v___y_5951_,
        v___y_5952_,
        v___y_5953_,
        v___y_5954_,
    );
    lean_dec(v___y_5954_);
    lean_dec_ref(v___y_5953_);
    lean_dec(v___y_5952_);
    lean_dec_ref(v___y_5951_);
    return v_res_5956_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_keys_5957_: *mut LeanObject,
    mut v_i_5958_: *mut LeanObject,
    mut v_k_5959_: *mut LeanObject,
) -> u8 {
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: u8 = 0;
    let mut v_k_x27_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5960_ = lean_array_get_size(v_keys_5957_);
                v___x_5961_ = lean_nat_dec_lt(v_i_5958_, v___x_5960_);
                if v___x_5961_ == 0 {
                    lean_dec(v_i_5958_);
                    return v___x_5961_;
                } else {
                    v_k_x27_5962_ = lean_array_fget_borrowed(v_keys_5957_, v_i_5958_);
                    v___x_5963_ = l_Lean_instBEqMVarId_beq(v_k_5959_, v_k_x27_5962_);
                    if v___x_5963_ == 0 {
                        v___x_5964_ = lean_unsigned_to_nat(1);
                        v___x_5965_ = lean_nat_add(v_i_5958_, v___x_5964_);
                        lean_dec(v_i_5958_);
                        v_i_5958_ = v___x_5965_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_5958_);
                        return v___x_5963_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_keys_5967_: *mut LeanObject,
    mut v_i_5968_: *mut LeanObject,
    mut v_k_5969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5970_: u8 = 0;
    let mut v_r_5971_: *mut LeanObject = core::ptr::null_mut();
    v_res_5970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_5967_, v_i_5968_, v_k_5969_);
    lean_dec(v_k_5969_);
    lean_dec_ref(v_keys_5967_);
    v_r_5971_ = lean_box((v_res_5970_) as usize);
    return v_r_5971_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_5972_: usize = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: usize = 0;
    v___x_5972_ = 5usize;
    v___x_5973_ = 1usize;
    v___x_5974_ = lean_usize_shift_left(v___x_5973_, v___x_5972_);
    return v___x_5974_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_5975_: usize = 0;
    let mut v___x_5976_: usize = 0;
    let mut v___x_5977_: usize = 0;
    v___x_5975_ = 1usize;
    v___x_5976_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_5977_ = lean_usize_sub(v___x_5976_, v___x_5975_);
    return v___x_5977_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(
    mut v_x_5978_: *mut LeanObject,
    mut v_x_5979_: usize,
    mut v_x_5980_: *mut LeanObject,
) -> u8 {
    let mut v_es_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: usize = 0;
    let mut v___x_5984_: usize = 0;
    let mut v___x_5985_: usize = 0;
    let mut v_j_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: u8 = 0;
    let mut v_node_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: usize = 0;
    let mut v___x_5993_: u8 = 0;
    let mut v_ks_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5978_) == 0 {
                    v_es_5981_ = lean_ctor_get(v_x_5978_, 0);
                    v___x_5982_ = lean_box(2);
                    v___x_5983_ = 5usize;
                    v___x_5984_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_5985_ = lean_usize_land(v_x_5979_, v___x_5984_);
                    v_j_5986_ = lean_usize_to_nat(v___x_5985_);
                    v___x_5987_ = lean_array_get_borrowed(v___x_5982_, v_es_5981_, v_j_5986_);
                    lean_dec(v_j_5986_);
                    match lean_obj_tag(v___x_5987_) {
                        0 => {
                            v_key_5988_ = lean_ctor_get(v___x_5987_, 0);
                            v___x_5989_ = l_Lean_instBEqMVarId_beq(v_x_5980_, v_key_5988_);
                            return v___x_5989_;
                        }
                        1 => {
                            v_node_5990_ = lean_ctor_get(v___x_5987_, 0);
                            v___x_5991_ = lean_usize_shift_right(v_x_5979_, v___x_5983_);
                            v_x_5978_ = v_node_5990_;
                            v_x_5979_ = v___x_5991_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5993_ = 0;
                            return v___x_5993_;
                        }
                    }
                } else {
                    v_ks_5994_ = lean_ctor_get(v_x_5978_, 0);
                    v___x_5995_ = lean_unsigned_to_nat(0);
                    v___x_5996_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_5994_, v___x_5995_, v_x_5980_);
                    return v___x_5996_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_5997_: *mut LeanObject,
    mut v_x_5998_: *mut LeanObject,
    mut v_x_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3351__boxed_6000_: usize = 0;
    let mut v_res_6001_: u8 = 0;
    let mut v_r_6002_: *mut LeanObject = core::ptr::null_mut();
    v_x_3351__boxed_6000_ = lean_unbox_usize(v_x_5998_);
    lean_dec(v_x_5998_);
    v_res_6001_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_5997_, v_x_3351__boxed_6000_, v_x_5999_);
    lean_dec(v_x_5999_);
    lean_dec_ref(v_x_5997_);
    v_r_6002_ = lean_box((v_res_6001_) as usize);
    return v_r_6002_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(
    mut v_x_6003_: *mut LeanObject,
    mut v_x_6004_: *mut LeanObject,
) -> u8 {
    let mut v___x_6005_: u64 = 0;
    let mut v___x_6006_: usize = 0;
    let mut v___x_6007_: u8 = 0;
    v___x_6005_ = l_Lean_instHashableMVarId_hash(v_x_6004_);
    v___x_6006_ = lean_uint64_to_usize(v___x_6005_);
    v___x_6007_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_6003_, v___x_6006_, v_x_6004_);
    return v___x_6007_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(
    mut v_x_6008_: *mut LeanObject,
    mut v_x_6009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6010_: u8 = 0;
    let mut v_r_6011_: *mut LeanObject = core::ptr::null_mut();
    v_res_6010_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_6008_, v_x_6009_);
    lean_dec(v_x_6009_);
    lean_dec_ref(v_x_6008_);
    v_r_6011_ = lean_box((v_res_6010_) as usize);
    return v_r_6011_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(
    mut v_mvarId_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: u8 = 0;
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    v___x_6015_ = lean_st_ref_get(v___y_6013_);
    v_mctx_6016_ = lean_ctor_get(v___x_6015_, 0);
    lean_inc_ref(v_mctx_6016_);
    lean_dec(v___x_6015_);
    v_eAssignment_6017_ = lean_ctor_get(v_mctx_6016_, 8);
    lean_inc_ref(v_eAssignment_6017_);
    lean_dec_ref(v_mctx_6016_);
    v___x_6018_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_6017_, v_mvarId_6012_);
    lean_dec_ref(v_eAssignment_6017_);
    v___x_6019_ = lean_box((v___x_6018_) as usize);
    v___x_6020_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6020_, 0, v___x_6019_);
    return v___x_6020_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(
    mut v_mvarId_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6024_: *mut LeanObject = core::ptr::null_mut();
    v_res_6024_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(
        v_mvarId_6021_,
        v___y_6022_,
    );
    lean_dec(v___y_6022_);
    lean_dec(v_mvarId_6021_);
    return v_res_6024_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    v___x_6026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0;
    v___x_6027_ = l_Lean_stringToMessageData(v___x_6026_);
    return v___x_6027_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    v___x_6029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2;
    v___x_6030_ = l_Lean_stringToMessageData(v___x_6029_);
    return v___x_6030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(
    mut v_as_6031_: *mut LeanObject,
    mut v_sz_6032_: usize,
    mut v_i_6033_: usize,
    mut v_b_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
    mut v___y_6037_: *mut LeanObject,
    mut v___y_6038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: usize = 0;
    let mut v___x_6043_: usize = 0;
    let mut v___x_6045_: u8 = 0;
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: u8 = 0;
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: u8 = 0;
    let mut v___x_6059_: u8 = 0;
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6072_: u8 = 0;
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6076_: u8 = 0;
    let mut v_a_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6080_: u8 = 0;
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6084_: u8 = 0;
    let mut v_a_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6088_: u8 = 0;
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6045_ = lean_usize_dec_lt(v_i_6033_, v_sz_6032_);
                if v___x_6045_ == 0 {
                    v___x_6046_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6046_, 0, v_b_6034_);
                    return v___x_6046_;
                } else {
                    v_a_6047_ = lean_array_uget_borrowed(v_as_6031_, v_i_6033_);
                    v___x_6048_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_6047_, v___y_6036_);
                    if lean_obj_tag(v___x_6048_) == 0 {
                        v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
                        lean_inc(v_a_6049_);
                        lean_dec_ref_known(v___x_6048_, 1);
                        v___x_6050_ = lean_box(0);
                        v___x_6051_ = (lean_unbox(v_a_6049_) as u8);
                        lean_dec(v_a_6049_);
                        if v___x_6051_ == 0 {
                            lean_inc(v_a_6047_);
                            v___x_6052_ = l_Lean_MVarId_getDecl(
                                v_a_6047_,
                                v___y_6035_,
                                v___y_6036_,
                                v___y_6037_,
                                v___y_6038_,
                            );
                            if lean_obj_tag(v___x_6052_) == 0 {
                                v_a_6053_ = lean_ctor_get(v___x_6052_, 0);
                                lean_inc(v_a_6053_);
                                lean_dec_ref_known(v___x_6052_, 1);
                                v_userName_6057_ = lean_ctor_get(v_a_6053_, 0);
                                lean_inc(v_userName_6057_);
                                lean_dec(v_a_6053_);
                                v___x_6058_ = l_Lean_Name_isAnonymous(v_userName_6057_);
                                if v___x_6058_ == 0 {
                                    v___x_6059_ = l_Lean_Name_hasMacroScopes(v_userName_6057_);
                                    lean_dec(v_userName_6057_);
                                    if v___x_6059_ == 0 {
                                        lean_inc(v_a_6047_);
                                        v___x_6060_ = l_Lean_MVarId_getDecl(
                                            v_a_6047_,
                                            v___y_6035_,
                                            v___y_6036_,
                                            v___y_6037_,
                                            v___y_6038_,
                                        );
                                        if lean_obj_tag(v___x_6060_) == 0 {
                                            v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
                                            lean_inc(v_a_6061_);
                                            lean_dec_ref_known(v___x_6060_, 1);
                                            v_userName_6062_ = lean_ctor_get(v_a_6061_, 0);
                                            lean_inc(v_userName_6062_);
                                            lean_dec(v_a_6061_);
                                            v___x_6063_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
                                            v___x_6064_ =
                                                l_Lean_MessageData_ofName(v_userName_6062_);
                                            v___x_6065_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_6065_, 0, v___x_6063_);
                                            lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                                            v___x_6066_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
                                            v___x_6067_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_6067_, 0, v___x_6065_);
                                            lean_ctor_set(v___x_6067_, 1, v___x_6066_);
                                            v___x_6068_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_6067_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
                                            if lean_obj_tag(v___x_6068_) == 0 {
                                                lean_dec_ref_known(v___x_6068_, 1);
                                                v_a_6041_ = v___x_6050_;
                                                state = 1;
                                                continue;
                                            } else {
                                                return v___x_6068_;
                                            }
                                        } else {
                                            v_a_6069_ = lean_ctor_get(v___x_6060_, 0);
                                            v_isSharedCheck_6076_ =
                                                (!lean_is_exclusive(v___x_6060_)) as u8;
                                            if v_isSharedCheck_6076_ == 0 {
                                                v___x_6071_ = v___x_6060_;
                                                v_isShared_6072_ = v_isSharedCheck_6076_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6069_);
                                                lean_dec(v___x_6060_);
                                                v___x_6071_ = lean_box(0);
                                                v_isShared_6072_ = v_isSharedCheck_6076_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_userName_6057_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_6077_ = lean_ctor_get(v___x_6052_, 0);
                                v_isSharedCheck_6084_ = (!lean_is_exclusive(v___x_6052_)) as u8;
                                if v_isSharedCheck_6084_ == 0 {
                                    v___x_6079_ = v___x_6052_;
                                    v_isShared_6080_ = v_isSharedCheck_6084_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_6077_);
                                    lean_dec(v___x_6052_);
                                    v___x_6079_ = lean_box(0);
                                    v_isShared_6080_ = v_isSharedCheck_6084_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_a_6041_ = v___x_6050_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6085_ = lean_ctor_get(v___x_6048_, 0);
                        v_isSharedCheck_6092_ = (!lean_is_exclusive(v___x_6048_)) as u8;
                        if v_isSharedCheck_6092_ == 0 {
                            v___x_6087_ = v___x_6048_;
                            v_isShared_6088_ = v_isSharedCheck_6092_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6085_);
                            lean_dec(v___x_6048_);
                            v___x_6087_ = lean_box(0);
                            v_isShared_6088_ = v_isSharedCheck_6092_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6042_ = 1usize;
                v___x_6043_ = lean_usize_add(v_i_6033_, v___x_6042_);
                v_i_6033_ = v___x_6043_;
                v_b_6034_ = v_a_6041_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6055_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
                v___x_6056_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                    v___x_6055_,
                    v___y_6035_,
                    v___y_6036_,
                    v___y_6037_,
                    v___y_6038_,
                );
                if lean_obj_tag(v___x_6056_) == 0 {
                    lean_dec_ref_known(v___x_6056_, 1);
                    v_a_6041_ = v___x_6050_;
                    state = 1;
                    continue;
                } else {
                    return v___x_6056_;
                }
            }
            3 => {
                if v_isShared_6072_ == 0 {
                    v___x_6074_ = v___x_6071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6069_);
                    v___x_6074_ = v_reuseFailAlloc_6075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6074_;
            }
            5 => {
                if v_isShared_6080_ == 0 {
                    v___x_6082_ = v___x_6079_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6083_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6083_, 0, v_a_6077_);
                    v___x_6082_ = v_reuseFailAlloc_6083_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6082_;
            }
            7 => {
                if v_isShared_6088_ == 0 {
                    v___x_6090_ = v___x_6087_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6091_, 0, v_a_6085_);
                    v___x_6090_ = v_reuseFailAlloc_6091_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(
    mut v_as_6093_: *mut LeanObject,
    mut v_sz_6094_: *mut LeanObject,
    mut v_i_6095_: *mut LeanObject,
    mut v_b_6096_: *mut LeanObject,
    mut v___y_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
    mut v___y_6099_: *mut LeanObject,
    mut v___y_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6102_: usize = 0;
    let mut v_i_boxed_6103_: usize = 0;
    let mut v_res_6104_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6102_ = lean_unbox_usize(v_sz_6094_);
    lean_dec(v_sz_6094_);
    v_i_boxed_6103_ = lean_unbox_usize(v_i_6095_);
    lean_dec(v_i_6095_);
    v_res_6104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_6093_, v_sz_boxed_6102_, v_i_boxed_6103_, v_b_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
    lean_dec(v___y_6100_);
    lean_dec_ref(v___y_6099_);
    lean_dec(v___y_6098_);
    lean_dec_ref(v___y_6097_);
    lean_dec_ref(v_as_6093_);
    return v_res_6104_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(
    mut v_sz_6105_: usize,
    mut v_i_6106_: usize,
    mut v_bs_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
    mut v___y_6109_: *mut LeanObject,
    mut v___y_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6113_: u8 = 0;
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: usize = 0;
    let mut v___x_6121_: usize = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6113_ = lean_usize_dec_lt(v_i_6106_, v_sz_6105_);
                if v___x_6113_ == 0 {
                    v___x_6114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6114_, 0, v_bs_6107_);
                    return v___x_6114_;
                } else {
                    v_v_6115_ = lean_array_uget_borrowed(v_bs_6107_, v_i_6106_);
                    lean_inc(v_v_6115_);
                    v___x_6116_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_6115_, v___y_6109_);
                    if lean_obj_tag(v___x_6116_) == 0 {
                        v_a_6117_ = lean_ctor_get(v___x_6116_, 0);
                        lean_inc(v_a_6117_);
                        lean_dec_ref_known(v___x_6116_, 1);
                        v___x_6118_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6119_ = lean_array_uset(v_bs_6107_, v_i_6106_, v___x_6118_);
                        v___x_6120_ = 1usize;
                        v___x_6121_ = lean_usize_add(v_i_6106_, v___x_6120_);
                        v___x_6122_ = lean_array_uset(v_bs_x27_6119_, v_i_6106_, v_a_6117_);
                        v_i_6106_ = v___x_6121_;
                        v_bs_6107_ = v___x_6122_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6107_);
                        v_a_6124_ = lean_ctor_get(v___x_6116_, 0);
                        v_isSharedCheck_6131_ = (!lean_is_exclusive(v___x_6116_)) as u8;
                        if v_isSharedCheck_6131_ == 0 {
                            v___x_6126_ = v___x_6116_;
                            v_isShared_6127_ = v_isSharedCheck_6131_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6124_);
                            lean_dec(v___x_6116_);
                            v___x_6126_ = lean_box(0);
                            v_isShared_6127_ = v_isSharedCheck_6131_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6127_ == 0 {
                    v___x_6129_ = v___x_6126_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
                    v___x_6129_ = v_reuseFailAlloc_6130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(
    mut v_sz_6132_: *mut LeanObject,
    mut v_i_6133_: *mut LeanObject,
    mut v_bs_6134_: *mut LeanObject,
    mut v___y_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
    mut v___y_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6140_: usize = 0;
    let mut v_i_boxed_6141_: usize = 0;
    let mut v_res_6142_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6140_ = lean_unbox_usize(v_sz_6132_);
    lean_dec(v_sz_6132_);
    v_i_boxed_6141_ = lean_unbox_usize(v_i_6133_);
    lean_dec(v_i_6133_);
    v_res_6142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_6140_, v_i_boxed_6141_, v_bs_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
    lean_dec(v___y_6138_);
    lean_dec_ref(v___y_6137_);
    lean_dec(v___y_6136_);
    lean_dec_ref(v___y_6135_);
    return v_res_6142_;
}
pub unsafe fn l_Lean_Meta_addImplicitTargets(
    mut v_elimInfo_6145_: *mut LeanObject,
    mut v_targets_6146_: *mut LeanObject,
    mut v_a_6147_: *mut LeanObject,
    mut v_a_6148_: *mut LeanObject,
    mut v_a_6149_: *mut LeanObject,
    mut v_a_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elimType_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6160_: usize = 0;
    let mut v___x_6161_: usize = 0;
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6163_: usize = 0;
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6168_: u8 = 0;
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6176_: u8 = 0;
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elimType_6152_ = lean_ctor_get(v_elimInfo_6145_, 1);
                lean_inc_ref(v_elimType_6152_);
                v___x_6153_ = lean_unsigned_to_nat(0);
                v___x_6154_ = l_Lean_Meta_addImplicitTargets___closed__0;
                v___x_6155_ =
                    l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(
                        v_elimInfo_6145_,
                        v_targets_6146_,
                        v_elimType_6152_,
                        v___x_6153_,
                        v___x_6153_,
                        v___x_6154_,
                        v___x_6154_,
                        v_a_6147_,
                        v_a_6148_,
                        v_a_6149_,
                        v_a_6150_,
                    );
                if lean_obj_tag(v___x_6155_) == 0 {
                    v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
                    lean_inc(v_a_6156_);
                    lean_dec_ref_known(v___x_6155_, 1);
                    v_fst_6157_ = lean_ctor_get(v_a_6156_, 0);
                    lean_inc(v_fst_6157_);
                    v_snd_6158_ = lean_ctor_get(v_a_6156_, 1);
                    lean_inc(v_snd_6158_);
                    lean_dec(v_a_6156_);
                    v___x_6159_ = lean_box(0);
                    v_sz_6160_ = lean_array_size(v_fst_6157_);
                    v___x_6161_ = 0usize;
                    v___x_6162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_6157_, v_sz_6160_, v___x_6161_, v___x_6159_, v_a_6147_, v_a_6148_, v_a_6149_, v_a_6150_);
                    lean_dec(v_fst_6157_);
                    if lean_obj_tag(v___x_6162_) == 0 {
                        lean_dec_ref_known(v___x_6162_, 1);
                        v_sz_6163_ = lean_array_size(v_snd_6158_);
                        v___x_6164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_6163_, v___x_6161_, v_snd_6158_, v_a_6147_, v_a_6148_, v_a_6149_, v_a_6150_);
                        return v___x_6164_;
                    } else {
                        lean_dec(v_snd_6158_);
                        v_a_6165_ = lean_ctor_get(v___x_6162_, 0);
                        v_isSharedCheck_6172_ = (!lean_is_exclusive(v___x_6162_)) as u8;
                        if v_isSharedCheck_6172_ == 0 {
                            v___x_6167_ = v___x_6162_;
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6165_);
                            lean_dec(v___x_6162_);
                            v___x_6167_ = lean_box(0);
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_6173_ = lean_ctor_get(v___x_6155_, 0);
                    v_isSharedCheck_6180_ = (!lean_is_exclusive(v___x_6155_)) as u8;
                    if v_isSharedCheck_6180_ == 0 {
                        v___x_6175_ = v___x_6155_;
                        v_isShared_6176_ = v_isSharedCheck_6180_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6173_);
                        lean_dec(v___x_6155_);
                        v___x_6175_ = lean_box(0);
                        v_isShared_6176_ = v_isSharedCheck_6180_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6168_ == 0 {
                    v___x_6170_ = v___x_6167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
                    v___x_6170_ = v_reuseFailAlloc_6171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6170_;
            }
            3 => {
                if v_isShared_6176_ == 0 {
                    v___x_6178_ = v___x_6175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6179_, 0, v_a_6173_);
                    v___x_6178_ = v_reuseFailAlloc_6179_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addImplicitTargets___boxed(
    mut v_elimInfo_6181_: *mut LeanObject,
    mut v_targets_6182_: *mut LeanObject,
    mut v_a_6183_: *mut LeanObject,
    mut v_a_6184_: *mut LeanObject,
    mut v_a_6185_: *mut LeanObject,
    mut v_a_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6188_: *mut LeanObject = core::ptr::null_mut();
    v_res_6188_ = l_Lean_Meta_addImplicitTargets(
        v_elimInfo_6181_,
        v_targets_6182_,
        v_a_6183_,
        v_a_6184_,
        v_a_6185_,
        v_a_6186_,
    );
    lean_dec(v_a_6186_);
    lean_dec_ref(v_a_6185_);
    lean_dec(v_a_6184_);
    lean_dec_ref(v_a_6183_);
    lean_dec_ref(v_targets_6182_);
    return v_res_6188_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(
    mut v_mvarId_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    v___x_6195_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(
        v_mvarId_6189_,
        v___y_6191_,
    );
    return v___x_6195_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(
    mut v_mvarId_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(
        v_mvarId_6196_,
        v___y_6197_,
        v___y_6198_,
        v___y_6199_,
        v___y_6200_,
    );
    lean_dec(v___y_6200_);
    lean_dec_ref(v___y_6199_);
    lean_dec(v___y_6198_);
    lean_dec_ref(v___y_6197_);
    lean_dec(v_mvarId_6196_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(
    mut v_00_u03b2_6203_: *mut LeanObject,
    mut v_x_6204_: *mut LeanObject,
    mut v_x_6205_: *mut LeanObject,
) -> u8 {
    let mut v___x_6206_: u8 = 0;
    v___x_6206_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_6204_, v_x_6205_);
    return v___x_6206_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(
    mut v_00_u03b2_6207_: *mut LeanObject,
    mut v_x_6208_: *mut LeanObject,
    mut v_x_6209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6210_: u8 = 0;
    let mut v_r_6211_: *mut LeanObject = core::ptr::null_mut();
    v_res_6210_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_6207_, v_x_6208_, v_x_6209_);
    lean_dec(v_x_6209_);
    lean_dec_ref(v_x_6208_);
    v_r_6211_ = lean_box((v_res_6210_) as usize);
    return v_r_6211_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(
    mut v_00_u03b2_6212_: *mut LeanObject,
    mut v_x_6213_: *mut LeanObject,
    mut v_x_6214_: usize,
    mut v_x_6215_: *mut LeanObject,
) -> u8 {
    let mut v___x_6216_: u8 = 0;
    v___x_6216_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_6213_, v_x_6214_, v_x_6215_);
    return v___x_6216_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_6217_: *mut LeanObject,
    mut v_x_6218_: *mut LeanObject,
    mut v_x_6219_: *mut LeanObject,
    mut v_x_6220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3700__boxed_6221_: usize = 0;
    let mut v_res_6222_: u8 = 0;
    let mut v_r_6223_: *mut LeanObject = core::ptr::null_mut();
    v_x_3700__boxed_6221_ = lean_unbox_usize(v_x_6219_);
    lean_dec(v_x_6219_);
    v_res_6222_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_6217_, v_x_6218_, v_x_3700__boxed_6221_, v_x_6220_);
    lean_dec(v_x_6220_);
    lean_dec_ref(v_x_6218_);
    v_r_6223_ = lean_box((v_res_6222_) as usize);
    return v_r_6223_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_6224_: *mut LeanObject,
    mut v_keys_6225_: *mut LeanObject,
    mut v_vals_6226_: *mut LeanObject,
    mut v_heq_6227_: *mut LeanObject,
    mut v_i_6228_: *mut LeanObject,
    mut v_k_6229_: *mut LeanObject,
) -> u8 {
    let mut v___x_6230_: u8 = 0;
    v___x_6230_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_6225_, v_i_6228_, v_k_6229_);
    return v___x_6230_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_6231_: *mut LeanObject,
    mut v_keys_6232_: *mut LeanObject,
    mut v_vals_6233_: *mut LeanObject,
    mut v_heq_6234_: *mut LeanObject,
    mut v_i_6235_: *mut LeanObject,
    mut v_k_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6237_: u8 = 0;
    let mut v_r_6238_: *mut LeanObject = core::ptr::null_mut();
    v_res_6237_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_6231_, v_keys_6232_, v_vals_6233_, v_heq_6234_, v_i_6235_, v_k_6236_);
    lean_dec(v_k_6236_);
    lean_dec_ref(v_vals_6233_);
    lean_dec_ref(v_keys_6232_);
    v_r_6238_ = lean_box((v_res_6237_) as usize);
    return v_r_6238_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_6247_: *mut LeanObject,
    mut v_x_6248_: *mut LeanObject,
    mut v_x_6249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6254_: u8 = 0;
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6249_) == 0 {
                    lean_dec(v_x_6247_);
                    return v_x_6248_;
                } else {
                    v_head_6250_ = lean_ctor_get(v_x_6249_, 0);
                    v_tail_6251_ = lean_ctor_get(v_x_6249_, 1);
                    v_isSharedCheck_6262_ = (!lean_is_exclusive(v_x_6249_)) as u8;
                    if v_isSharedCheck_6262_ == 0 {
                        v___x_6253_ = v_x_6249_;
                        v_isShared_6254_ = v_isSharedCheck_6262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6251_);
                        lean_inc(v_head_6250_);
                        lean_dec(v_x_6249_);
                        v___x_6253_ = lean_box(0);
                        v_isShared_6254_ = v_isSharedCheck_6262_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6247_);
                if v_isShared_6254_ == 0 {
                    lean_ctor_set_tag(v___x_6253_, 5);
                    lean_ctor_set(v___x_6253_, 1, v_x_6247_);
                    lean_ctor_set(v___x_6253_, 0, v_x_6248_);
                    v___x_6256_ = v___x_6253_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6261_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_x_6248_);
                    lean_ctor_set(v_reuseFailAlloc_6261_, 1, v_x_6247_);
                    v___x_6256_ = v_reuseFailAlloc_6261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6257_ = lean_unsigned_to_nat(0);
                v___x_6258_ = l_Lean_Name_reprPrec(v_head_6250_, v___x_6257_);
                v___x_6259_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6259_, 0, v___x_6256_);
                lean_ctor_set(v___x_6259_, 1, v___x_6258_);
                v_x_6248_ = v___x_6259_;
                v_x_6249_ = v_tail_6251_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(
    mut v_x_6263_: *mut LeanObject,
    mut v_x_6264_: *mut LeanObject,
    mut v_x_6265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6270_: u8 = 0;
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6265_) == 0 {
                    lean_dec(v_x_6263_);
                    return v_x_6264_;
                } else {
                    v_head_6266_ = lean_ctor_get(v_x_6265_, 0);
                    v_tail_6267_ = lean_ctor_get(v_x_6265_, 1);
                    v_isSharedCheck_6278_ = (!lean_is_exclusive(v_x_6265_)) as u8;
                    if v_isSharedCheck_6278_ == 0 {
                        v___x_6269_ = v_x_6265_;
                        v_isShared_6270_ = v_isSharedCheck_6278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6267_);
                        lean_inc(v_head_6266_);
                        lean_dec(v_x_6265_);
                        v___x_6269_ = lean_box(0);
                        v_isShared_6270_ = v_isSharedCheck_6278_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6263_);
                if v_isShared_6270_ == 0 {
                    lean_ctor_set_tag(v___x_6269_, 5);
                    lean_ctor_set(v___x_6269_, 1, v_x_6263_);
                    lean_ctor_set(v___x_6269_, 0, v_x_6264_);
                    v___x_6272_ = v___x_6269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6277_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_x_6264_);
                    lean_ctor_set(v_reuseFailAlloc_6277_, 1, v_x_6263_);
                    v___x_6272_ = v_reuseFailAlloc_6277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6273_ = lean_unsigned_to_nat(0);
                v___x_6274_ = l_Lean_Name_reprPrec(v_head_6266_, v___x_6273_);
                v___x_6275_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6275_, 0, v___x_6272_);
                lean_ctor_set(v___x_6275_, 1, v___x_6274_);
                v___x_6276_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_6263_, v___x_6275_, v_tail_6267_);
                return v___x_6276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(
    mut v___y_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    v___x_6280_ = lean_unsigned_to_nat(0);
    v___x_6281_ = l_Lean_Name_reprPrec(v___y_6279_, v___x_6280_);
    return v___x_6281_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(
    mut v_x_6282_: *mut LeanObject,
    mut v_x_6283_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6282_) == 0 {
        let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_6283_);
        v___x_6284_ = lean_box(0);
        return v___x_6284_;
    } else {
        let mut v_tail_6285_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6285_ = lean_ctor_get(v_x_6282_, 1);
        if lean_obj_tag(v_tail_6285_) == 0 {
            let mut v_head_6286_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_6283_);
            v_head_6286_ = lean_ctor_get(v_x_6282_, 0);
            lean_inc(v_head_6286_);
            lean_dec_ref_known(v_x_6282_, 2);
            v___x_6287_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_6286_);
            return v___x_6287_;
        } else {
            let mut v_head_6288_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_6285_);
            v_head_6288_ = lean_ctor_get(v_x_6282_, 0);
            lean_inc(v_head_6288_);
            lean_dec_ref_known(v_x_6282_, 2);
            v___x_6289_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_6288_);
            v___x_6290_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_6283_, v___x_6289_, v_tail_6285_);
            return v___x_6290_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(
    mut v_xs_6291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: u8 = 0;
    v___x_6292_ = lean_array_get_size(v_xs_6291_);
    v___x_6293_ = lean_unsigned_to_nat(0);
    v___x_6294_ = lean_nat_dec_eq(v___x_6292_, v___x_6293_);
    if v___x_6294_ == 0 {
        let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
        v___x_6295_ = lean_array_to_list(v_xs_6291_);
        v___x_6296_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
        v___x_6297_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_6295_, v___x_6296_);
        v___x_6298_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4,
        );
        v___x_6299_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5;
        v___x_6300_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_6300_, 0, v___x_6299_);
        lean_ctor_set(v___x_6300_, 1, v___x_6297_);
        v___x_6301_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6;
        v___x_6302_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_6302_, 0, v___x_6300_);
        lean_ctor_set(v___x_6302_, 1, v___x_6301_);
        v___x_6303_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_6303_, 0, v___x_6298_);
        lean_ctor_set(v___x_6303_, 1, v___x_6302_);
        v___x_6304_ = l_Std_Format_fill(v___x_6303_);
        return v___x_6304_;
    } else {
        let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_6291_);
        v___x_6305_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8;
        return v___x_6305_;
    }
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminator_repr___redArg(
    mut v_x_6320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_induction_6321_: u8 = 0;
    let mut v_typeNames_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimName_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: u8 = 0;
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    v_induction_6321_ = lean_ctor_get_uint8(
        v_x_6320_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_typeNames_6322_ = lean_ctor_get(v_x_6320_, 0);
    lean_inc_ref(v_typeNames_6322_);
    v_elimName_6323_ = lean_ctor_get(v_x_6320_, 1);
    lean_inc(v_elimName_6323_);
    lean_dec_ref(v_x_6320_);
    v___x_6324_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5;
    v___x_6325_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2;
    v___x_6326_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12,
    );
    v___x_6327_ = lean_unsigned_to_nat(0);
    v___x_6328_ = l_Bool_repr___redArg(v_induction_6321_);
    v___x_6329_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6329_, 0, v___x_6326_);
    lean_ctor_set(v___x_6329_, 1, v___x_6328_);
    v___x_6330_ = 0;
    v___x_6331_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6331_, 0, v___x_6329_);
    lean_ctor_set_uint8(
        v___x_6331_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6330_,
    );
    v___x_6332_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6332_, 0, v___x_6325_);
    lean_ctor_set(v___x_6332_, 1, v___x_6331_);
    v___x_6333_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9;
    v___x_6334_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6334_, 0, v___x_6332_);
    lean_ctor_set(v___x_6334_, 1, v___x_6333_);
    v___x_6335_ = lean_box(1);
    v___x_6336_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6336_, 0, v___x_6334_);
    lean_ctor_set(v___x_6336_, 1, v___x_6335_);
    v___x_6337_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4;
    v___x_6338_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6338_, 0, v___x_6336_);
    lean_ctor_set(v___x_6338_, 1, v___x_6337_);
    v___x_6339_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6339_, 0, v___x_6338_);
    lean_ctor_set(v___x_6339_, 1, v___x_6324_);
    v___x_6340_ =
        l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_6322_);
    v___x_6341_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6341_, 0, v___x_6326_);
    lean_ctor_set(v___x_6341_, 1, v___x_6340_);
    v___x_6342_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6342_, 0, v___x_6341_);
    lean_ctor_set_uint8(
        v___x_6342_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6330_,
    );
    v___x_6343_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6343_, 0, v___x_6339_);
    lean_ctor_set(v___x_6343_, 1, v___x_6342_);
    v___x_6344_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6344_, 0, v___x_6343_);
    lean_ctor_set(v___x_6344_, 1, v___x_6333_);
    v___x_6345_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6345_, 0, v___x_6344_);
    lean_ctor_set(v___x_6345_, 1, v___x_6335_);
    v___x_6346_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6;
    v___x_6347_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6347_, 0, v___x_6345_);
    lean_ctor_set(v___x_6347_, 1, v___x_6346_);
    v___x_6348_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6348_, 0, v___x_6347_);
    lean_ctor_set(v___x_6348_, 1, v___x_6324_);
    v___x_6349_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once),
        _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4,
    );
    v___x_6350_ = l_Lean_Name_reprPrec(v_elimName_6323_, v___x_6327_);
    v___x_6351_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6351_, 0, v___x_6349_);
    lean_ctor_set(v___x_6351_, 1, v___x_6350_);
    v___x_6352_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6352_, 0, v___x_6351_);
    lean_ctor_set_uint8(
        v___x_6352_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6330_,
    );
    v___x_6353_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6353_, 0, v___x_6348_);
    lean_ctor_set(v___x_6353_, 1, v___x_6352_);
    v___x_6354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20,
    );
    v___x_6355_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21;
    v___x_6356_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6356_, 0, v___x_6355_);
    lean_ctor_set(v___x_6356_, 1, v___x_6353_);
    v___x_6357_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22;
    v___x_6358_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6358_, 0, v___x_6356_);
    lean_ctor_set(v___x_6358_, 1, v___x_6357_);
    v___x_6359_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6359_, 0, v___x_6354_);
    lean_ctor_set(v___x_6359_, 1, v___x_6358_);
    v___x_6360_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6360_, 0, v___x_6359_);
    lean_ctor_set_uint8(
        v___x_6360_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6330_,
    );
    return v___x_6360_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminator_repr(
    mut v_x_6361_: *mut LeanObject,
    mut v_prec_6362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    v___x_6363_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_6361_);
    return v___x_6363_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminator_repr___boxed(
    mut v_x_6364_: *mut LeanObject,
    mut v_prec_6365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6366_: *mut LeanObject = core::ptr::null_mut();
    v_res_6366_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_6364_, v_prec_6365_);
    lean_dec(v_prec_6365_);
    return v_res_6366_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0()
-> *mut LeanObject {
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    v___x_6369_ = lean_box(0);
    v___x_6370_ = lean_unsigned_to_nat(16);
    v___x_6371_ = lean_mk_array(v___x_6370_, v___x_6369_);
    return v___x_6371_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1()
-> *mut LeanObject {
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    v___x_6372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0,
    );
    v___x_6373_ = lean_unsigned_to_nat(0);
    v___x_6374_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6374_, 0, v___x_6373_);
    lean_ctor_set(v___x_6374_, 1, v___x_6372_);
    return v___x_6374_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2()
-> *mut LeanObject {
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    v___x_6375_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6375_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3()
-> *mut LeanObject {
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    v___x_6376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2,
    );
    v___x_6377_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6377_, 0, v___x_6376_);
    return v___x_6377_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4()
-> *mut LeanObject {
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    v___x_6378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3,
    );
    v___x_6379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1,
    );
    v___x_6380_ = 1;
    v___x_6381_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_6381_, 0, v___x_6379_);
    lean_ctor_set(v___x_6381_, 1, v___x_6378_);
    lean_ctor_set_uint8(
        v___x_6381_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_6380_,
    );
    return v___x_6381_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators_default() -> *mut LeanObject {
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    v___x_6382_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4,
    );
    return v___x_6382_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCustomEliminators() -> *mut LeanObject {
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    v___x_6383_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
    return v___x_6383_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v_f_6384_: *mut LeanObject,
    mut v_x1_6385_: *mut LeanObject,
    mut v_x2_6386_: *mut LeanObject,
    mut v_x3_6387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    v___x_6388_ = lean_apply_3(v_f_6384_, v_x1_6385_, v_x2_6386_, v_x3_6387_);
    return v___x_6388_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(
    mut v_f_6389_: *mut LeanObject,
    mut v_keys_6390_: *mut LeanObject,
    mut v_vals_6391_: *mut LeanObject,
    mut v_i_6392_: *mut LeanObject,
    mut v_acc_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: u8 = 0;
    let mut v_k_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6394_ = lean_array_get_size(v_keys_6390_);
                v___x_6395_ = lean_nat_dec_lt(v_i_6392_, v___x_6394_);
                if v___x_6395_ == 0 {
                    lean_dec(v_i_6392_);
                    lean_dec(v_f_6389_);
                    return v_acc_6393_;
                } else {
                    v_k_6396_ = lean_array_fget_borrowed(v_keys_6390_, v_i_6392_);
                    v_v_6397_ = lean_array_fget_borrowed(v_vals_6391_, v_i_6392_);
                    lean_inc(v_f_6389_);
                    lean_inc(v_v_6397_);
                    lean_inc(v_k_6396_);
                    v___x_6398_ = lean_apply_3(v_f_6389_, v_acc_6393_, v_k_6396_, v_v_6397_);
                    v___x_6399_ = lean_unsigned_to_nat(1);
                    v___x_6400_ = lean_nat_add(v_i_6392_, v___x_6399_);
                    lean_dec(v_i_6392_);
                    v_i_6392_ = v___x_6400_;
                    v_acc_6393_ = v___x_6398_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(
    mut v_f_6402_: *mut LeanObject,
    mut v_keys_6403_: *mut LeanObject,
    mut v_vals_6404_: *mut LeanObject,
    mut v_i_6405_: *mut LeanObject,
    mut v_acc_6406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6407_: *mut LeanObject = core::ptr::null_mut();
    v_res_6407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_6402_, v_keys_6403_, v_vals_6404_, v_i_6405_, v_acc_6406_);
    lean_dec_ref(v_vals_6404_);
    lean_dec_ref(v_keys_6403_);
    return v_res_6407_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(
    mut v_f_6408_: *mut LeanObject,
    mut v_x_6409_: *mut LeanObject,
    mut v_x_6410_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6409_) == 0 {
        let mut v_es_6411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6414_: u8 = 0;
        v_es_6411_ = lean_ctor_get(v_x_6409_, 0);
        v___x_6412_ = lean_unsigned_to_nat(0);
        v___x_6413_ = lean_array_get_size(v_es_6411_);
        v___x_6414_ = lean_nat_dec_lt(v___x_6412_, v___x_6413_);
        if v___x_6414_ == 0 {
            lean_dec(v_f_6408_);
            return v_x_6410_;
        } else {
            let mut v___x_6415_: u8 = 0;
            v___x_6415_ = lean_nat_dec_le(v___x_6413_, v___x_6413_);
            if v___x_6415_ == 0 {
                if v___x_6414_ == 0 {
                    lean_dec(v_f_6408_);
                    return v_x_6410_;
                } else {
                    let mut v___x_6416_: usize = 0;
                    let mut v___x_6417_: usize = 0;
                    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
                    v___x_6416_ = 0usize;
                    v___x_6417_ = lean_usize_of_nat(v___x_6413_);
                    v___x_6418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_6408_, v_es_6411_, v___x_6416_, v___x_6417_, v_x_6410_);
                    return v___x_6418_;
                }
            } else {
                let mut v___x_6419_: usize = 0;
                let mut v___x_6420_: usize = 0;
                let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
                v___x_6419_ = 0usize;
                v___x_6420_ = lean_usize_of_nat(v___x_6413_);
                v___x_6421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_6408_, v_es_6411_, v___x_6419_, v___x_6420_, v_x_6410_);
                return v___x_6421_;
            }
        }
    } else {
        let mut v_ks_6422_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_6423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
        v_ks_6422_ = lean_ctor_get(v_x_6409_, 0);
        v_vs_6423_ = lean_ctor_get(v_x_6409_, 1);
        v___x_6424_ = lean_unsigned_to_nat(0);
        v___x_6425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_6408_, v_ks_6422_, v_vs_6423_, v___x_6424_, v_x_6410_);
        return v___x_6425_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(
    mut v_f_6426_: *mut LeanObject,
    mut v_as_6427_: *mut LeanObject,
    mut v_i_6428_: usize,
    mut v_stop_6429_: usize,
    mut v_b_6430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: usize = 0;
    let mut v___x_6434_: usize = 0;
    let mut v___x_6436_: u8 = 0;
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6436_ = lean_usize_dec_eq(v_i_6428_, v_stop_6429_);
                if v___x_6436_ == 0 {
                    v___x_6437_ = lean_array_uget_borrowed(v_as_6427_, v_i_6428_);
                    match lean_obj_tag(v___x_6437_) {
                        0 => {
                            v_key_6438_ = lean_ctor_get(v___x_6437_, 0);
                            v_val_6439_ = lean_ctor_get(v___x_6437_, 1);
                            lean_inc(v_f_6426_);
                            lean_inc(v_val_6439_);
                            lean_inc(v_key_6438_);
                            v___x_6440_ =
                                lean_apply_3(v_f_6426_, v_b_6430_, v_key_6438_, v_val_6439_);
                            v___y_6432_ = v___x_6440_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_6441_ = lean_ctor_get(v___x_6437_, 0);
                            lean_inc(v_f_6426_);
                            v___x_6442_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_6426_, v_node_6441_, v_b_6430_);
                            v___y_6432_ = v___x_6442_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_6432_ = v_b_6430_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_f_6426_);
                    return v_b_6430_;
                }
            }
            1 => {
                v___x_6433_ = 1usize;
                v___x_6434_ = lean_usize_add(v_i_6428_, v___x_6433_);
                v_i_6428_ = v___x_6434_;
                v_b_6430_ = v___y_6432_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(
    mut v_f_6443_: *mut LeanObject,
    mut v_as_6444_: *mut LeanObject,
    mut v_i_6445_: *mut LeanObject,
    mut v_stop_6446_: *mut LeanObject,
    mut v_b_6447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6448_: usize = 0;
    let mut v_stop_boxed_6449_: usize = 0;
    let mut v_res_6450_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6448_ = lean_unbox_usize(v_i_6445_);
    lean_dec(v_i_6445_);
    v_stop_boxed_6449_ = lean_unbox_usize(v_stop_6446_);
    lean_dec(v_stop_6446_);
    v_res_6450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_6443_, v_as_6444_, v_i_boxed_6448_, v_stop_boxed_6449_, v_b_6447_);
    lean_dec_ref(v_as_6444_);
    return v_res_6450_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_f_6451_: *mut LeanObject,
    mut v_x_6452_: *mut LeanObject,
    mut v_x_6453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6454_: *mut LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_6451_, v_x_6452_, v_x_6453_);
    lean_dec_ref(v_x_6452_);
    return v_res_6454_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(
    mut v_map_6455_: *mut LeanObject,
    mut v_f_6456_: *mut LeanObject,
    mut v_init_6457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    v___f_6458_ = lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_6458_, 0, v_f_6456_);
    v___x_6459_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_6458_, v_map_6455_, v_init_6457_);
    return v___x_6459_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_map_6460_: *mut LeanObject,
    mut v_f_6461_: *mut LeanObject,
    mut v_init_6462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6463_: *mut LeanObject = core::ptr::null_mut();
    v_res_6463_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_6460_, v_f_6461_, v_init_6462_);
    lean_dec_ref(v_map_6460_);
    return v_res_6463_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(
    mut v_f_6464_: *mut LeanObject,
    mut v_x_6465_: *mut LeanObject,
    mut v_x_6466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6466_) == 0 {
                    lean_dec(v_f_6464_);
                    return v_x_6465_;
                } else {
                    v_key_6467_ = lean_ctor_get(v_x_6466_, 0);
                    lean_inc(v_key_6467_);
                    v_value_6468_ = lean_ctor_get(v_x_6466_, 1);
                    lean_inc(v_value_6468_);
                    v_tail_6469_ = lean_ctor_get(v_x_6466_, 2);
                    lean_inc(v_tail_6469_);
                    lean_dec_ref_known(v_x_6466_, 3);
                    lean_inc(v_f_6464_);
                    v___x_6470_ = lean_apply_3(v_f_6464_, v_x_6465_, v_key_6467_, v_value_6468_);
                    v_x_6465_ = v___x_6470_;
                    v_x_6466_ = v_tail_6469_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(
    mut v_f_6472_: *mut LeanObject,
    mut v_as_6473_: *mut LeanObject,
    mut v_i_6474_: usize,
    mut v_stop_6475_: usize,
    mut v_b_6476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6477_ = lean_usize_dec_eq(v_i_6474_, v_stop_6475_);
                if v___x_6477_ == 0 {
                    v___x_6478_ = lean_array_uget_borrowed(v_as_6473_, v_i_6474_);
                    lean_inc(v___x_6478_);
                    lean_inc(v_f_6472_);
                    v___x_6479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_6472_, v_b_6476_, v___x_6478_);
                    v___x_6480_ = 1usize;
                    v___x_6481_ = lean_usize_add(v_i_6474_, v___x_6480_);
                    v_i_6474_ = v___x_6481_;
                    v_b_6476_ = v___x_6479_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_f_6472_);
                    return v_b_6476_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_f_6483_: *mut LeanObject,
    mut v_as_6484_: *mut LeanObject,
    mut v_i_6485_: *mut LeanObject,
    mut v_stop_6486_: *mut LeanObject,
    mut v_b_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6488_: usize = 0;
    let mut v_stop_boxed_6489_: usize = 0;
    let mut v_res_6490_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6488_ = lean_unbox_usize(v_i_6485_);
    lean_dec(v_i_6485_);
    v_stop_boxed_6489_ = lean_unbox_usize(v_stop_6486_);
    lean_dec(v_stop_6486_);
    v_res_6490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_6483_, v_as_6484_, v_i_boxed_6488_, v_stop_boxed_6489_, v_b_6487_);
    lean_dec_ref(v_as_6484_);
    return v_res_6490_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(
    mut v_f_6491_: *mut LeanObject,
    mut v_init_6492_: *mut LeanObject,
    mut v_m_6493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_u2081_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: u8 = 0;
    v_map_u2081_6494_ = lean_ctor_get(v_m_6493_, 0);
    v_map_u2082_6495_ = lean_ctor_get(v_m_6493_, 1);
    v_buckets_6496_ = lean_ctor_get(v_map_u2081_6494_, 1);
    v___x_6497_ = lean_unsigned_to_nat(0);
    v___x_6498_ = lean_array_get_size(v_buckets_6496_);
    v___x_6499_ = lean_nat_dec_lt(v___x_6497_, v___x_6498_);
    if v___x_6499_ == 0 {
        let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
        v___x_6500_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_6495_, v_f_6491_, v_init_6492_);
        return v___x_6500_;
    } else {
        let mut v___x_6501_: u8 = 0;
        v___x_6501_ = lean_nat_dec_le(v___x_6498_, v___x_6498_);
        if v___x_6501_ == 0 {
            if v___x_6499_ == 0 {
                let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
                v___x_6502_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_6495_, v_f_6491_, v_init_6492_);
                return v___x_6502_;
            } else {
                let mut v___x_6503_: usize = 0;
                let mut v___x_6504_: usize = 0;
                let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
                v___x_6503_ = 0usize;
                v___x_6504_ = lean_usize_of_nat(v___x_6498_);
                lean_inc(v_f_6491_);
                v___x_6505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_6491_, v_buckets_6496_, v___x_6503_, v___x_6504_, v_init_6492_);
                v___x_6506_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_6495_, v_f_6491_, v___x_6505_);
                return v___x_6506_;
            }
        } else {
            let mut v___x_6507_: usize = 0;
            let mut v___x_6508_: usize = 0;
            let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
            v___x_6507_ = 0usize;
            v___x_6508_ = lean_usize_of_nat(v___x_6498_);
            lean_inc(v_f_6491_);
            v___x_6509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_6491_, v_buckets_6496_, v___x_6507_, v___x_6508_, v_init_6492_);
            v___x_6510_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_6495_, v_f_6491_, v___x_6509_);
            return v___x_6510_;
        }
    }
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(
    mut v_f_6511_: *mut LeanObject,
    mut v_init_6512_: *mut LeanObject,
    mut v_m_6513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6514_: *mut LeanObject = core::ptr::null_mut();
    v_res_6514_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_6511_, v_init_6512_, v_m_6513_);
    lean_dec_ref(v_m_6513_);
    return v_res_6514_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(
    mut v_es_6515_: *mut LeanObject,
    mut v_a_6516_: *mut LeanObject,
    mut v_b_6517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    v___x_6518_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6518_, 0, v_a_6516_);
    lean_ctor_set(v___x_6518_, 1, v_b_6517_);
    v___x_6519_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6519_, 0, v___x_6518_);
    lean_ctor_set(v___x_6519_, 1, v_es_6515_);
    return v___x_6519_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(
    mut v_m_6521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    v___f_6522_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0;
    v___x_6523_ = lean_box(0);
    v___x_6524_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_6522_, v___x_6523_, v_m_6521_);
    return v___x_6524_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(
    mut v_m_6525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6526_: *mut LeanObject = core::ptr::null_mut();
    v_res_6526_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(
            v_m_6525_,
        );
    lean_dec_ref(v_m_6525_);
    return v_res_6526_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(
    mut v_x_6527_: *mut LeanObject,
    mut v_x_6528_: *mut LeanObject,
    mut v_x_6529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6534_: u8 = 0;
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6529_) == 0 {
                    lean_dec(v_x_6527_);
                    return v_x_6528_;
                } else {
                    v_head_6530_ = lean_ctor_get(v_x_6529_, 0);
                    v_tail_6531_ = lean_ctor_get(v_x_6529_, 1);
                    v_isSharedCheck_6540_ = (!lean_is_exclusive(v_x_6529_)) as u8;
                    if v_isSharedCheck_6540_ == 0 {
                        v___x_6533_ = v_x_6529_;
                        v_isShared_6534_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6531_);
                        lean_inc(v_head_6530_);
                        lean_dec(v_x_6529_);
                        v___x_6533_ = lean_box(0);
                        v_isShared_6534_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6527_);
                if v_isShared_6534_ == 0 {
                    lean_ctor_set_tag(v___x_6533_, 5);
                    lean_ctor_set(v___x_6533_, 1, v_x_6527_);
                    lean_ctor_set(v___x_6533_, 0, v_x_6528_);
                    v___x_6536_ = v___x_6533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6539_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6539_, 0, v_x_6528_);
                    lean_ctor_set(v_reuseFailAlloc_6539_, 1, v_x_6527_);
                    v___x_6536_ = v_reuseFailAlloc_6539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6537_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6537_, 0, v___x_6536_);
                lean_ctor_set(v___x_6537_, 1, v_head_6530_);
                v_x_6528_ = v___x_6537_;
                v_x_6529_ = v_tail_6531_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(
    mut v_x_6541_: *mut LeanObject,
    mut v_x_6542_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6541_) == 0 {
        let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_6542_);
        v___x_6543_ = lean_box(0);
        return v___x_6543_;
    } else {
        let mut v_tail_6544_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6544_ = lean_ctor_get(v_x_6541_, 1);
        if lean_obj_tag(v_tail_6544_) == 0 {
            let mut v_head_6545_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_6542_);
            v_head_6545_ = lean_ctor_get(v_x_6541_, 0);
            lean_inc(v_head_6545_);
            lean_dec_ref_known(v_x_6541_, 2);
            return v_head_6545_;
        } else {
            let mut v_head_6546_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_6544_);
            v_head_6546_ = lean_ctor_get(v_x_6541_, 0);
            lean_inc(v_head_6546_);
            lean_dec_ref_known(v_x_6541_, 2);
            v___x_6547_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(v_x_6542_, v_head_6546_, v_tail_6544_);
            return v___x_6547_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    v___x_6550_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0;
    v___x_6551_ = lean_string_length(v___x_6550_);
    return v___x_6551_;
}
pub unsafe fn _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    v___x_6552_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once), _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2);
    v___x_6553_ = lean_nat_to_int(v___x_6552_);
    return v___x_6553_;
}
pub unsafe fn l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(
    mut v_x_6558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v___x_6564_: u8 = 0;
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6559_ = lean_ctor_get(v_x_6558_, 0);
                v_snd_6560_ = lean_ctor_get(v_x_6558_, 1);
                v_isSharedCheck_6583_ = (!lean_is_exclusive(v_x_6558_)) as u8;
                if v_isSharedCheck_6583_ == 0 {
                    v___x_6562_ = v_x_6558_;
                    v_isShared_6563_ = v_isSharedCheck_6583_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_6560_);
                    lean_inc(v_fst_6559_);
                    lean_dec(v_x_6558_);
                    v___x_6562_ = lean_box(0);
                    v_isShared_6563_ = v_isSharedCheck_6583_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6564_ = (lean_unbox(v_fst_6559_) as u8);
                lean_dec(v_fst_6559_);
                v___x_6565_ = l_Bool_repr___redArg(v___x_6564_);
                v___x_6566_ = lean_box(0);
                if v_isShared_6563_ == 0 {
                    lean_ctor_set_tag(v___x_6562_, 1);
                    lean_ctor_set(v___x_6562_, 1, v___x_6566_);
                    lean_ctor_set(v___x_6562_, 0, v___x_6565_);
                    v___x_6568_ = v___x_6562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6582_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6582_, 0, v___x_6565_);
                    lean_ctor_set(v_reuseFailAlloc_6582_, 1, v___x_6566_);
                    v___x_6568_ = v_reuseFailAlloc_6582_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6569_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(
                    v_snd_6560_,
                );
                v___x_6570_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6570_, 0, v___x_6569_);
                lean_ctor_set(v___x_6570_, 1, v___x_6568_);
                v___x_6571_ = l_List_reverse___redArg(v___x_6570_);
                v___x_6572_ =
                    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
                v___x_6573_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_6571_, v___x_6572_);
                v___x_6574_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once), _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
                v___x_6575_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4;
                v___x_6576_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6576_, 0, v___x_6575_);
                lean_ctor_set(v___x_6576_, 1, v___x_6573_);
                v___x_6577_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5;
                v___x_6578_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6578_, 0, v___x_6576_);
                lean_ctor_set(v___x_6578_, 1, v___x_6577_);
                v___x_6579_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6579_, 0, v___x_6574_);
                lean_ctor_set(v___x_6579_, 1, v___x_6578_);
                v___x_6580_ = 0;
                v___x_6581_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_6581_, 0, v___x_6579_);
                lean_ctor_set_uint8(
                    v___x_6581_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6580_,
                );
                return v___x_6581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(
    mut v_x_6584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: u8 = 0;
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6585_ = lean_ctor_get(v_x_6584_, 0);
                v_snd_6586_ = lean_ctor_get(v_x_6584_, 1);
                v_isSharedCheck_6609_ = (!lean_is_exclusive(v_x_6584_)) as u8;
                if v_isSharedCheck_6609_ == 0 {
                    v___x_6588_ = v_x_6584_;
                    v_isShared_6589_ = v_isSharedCheck_6609_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_6586_);
                    lean_inc(v_fst_6585_);
                    lean_dec(v_x_6584_);
                    v___x_6588_ = lean_box(0);
                    v_isShared_6589_ = v_isSharedCheck_6609_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6590_ = lean_unsigned_to_nat(0);
                v___x_6591_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_fst_6585_);
                v___x_6592_ = lean_box(0);
                if v_isShared_6589_ == 0 {
                    lean_ctor_set_tag(v___x_6588_, 1);
                    lean_ctor_set(v___x_6588_, 1, v___x_6592_);
                    lean_ctor_set(v___x_6588_, 0, v___x_6591_);
                    v___x_6594_ = v___x_6588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6608_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6608_, 0, v___x_6591_);
                    lean_ctor_set(v_reuseFailAlloc_6608_, 1, v___x_6592_);
                    v___x_6594_ = v_reuseFailAlloc_6608_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6595_ = l_Lean_Name_reprPrec(v_snd_6586_, v___x_6590_);
                v___x_6596_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6596_, 0, v___x_6595_);
                lean_ctor_set(v___x_6596_, 1, v___x_6594_);
                v___x_6597_ = l_List_reverse___redArg(v___x_6596_);
                v___x_6598_ =
                    l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
                v___x_6599_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_6597_, v___x_6598_);
                v___x_6600_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once), _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
                v___x_6601_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4;
                v___x_6602_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6602_, 0, v___x_6601_);
                lean_ctor_set(v___x_6602_, 1, v___x_6599_);
                v___x_6603_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5;
                v___x_6604_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6604_, 0, v___x_6602_);
                lean_ctor_set(v___x_6604_, 1, v___x_6603_);
                v___x_6605_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6605_, 0, v___x_6600_);
                lean_ctor_set(v___x_6605_, 1, v___x_6604_);
                v___x_6606_ = 0;
                v___x_6607_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_6607_, 0, v___x_6605_);
                lean_ctor_set_uint8(
                    v___x_6607_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6606_,
                );
                return v___x_6607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(
    mut v_x_6610_: *mut LeanObject,
    mut v_x_6611_: *mut LeanObject,
    mut v_x_6612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6617_: u8 = 0;
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6612_) == 0 {
                    lean_dec(v_x_6610_);
                    return v_x_6611_;
                } else {
                    v_head_6613_ = lean_ctor_get(v_x_6612_, 0);
                    v_tail_6614_ = lean_ctor_get(v_x_6612_, 1);
                    v_isSharedCheck_6624_ = (!lean_is_exclusive(v_x_6612_)) as u8;
                    if v_isSharedCheck_6624_ == 0 {
                        v___x_6616_ = v_x_6612_;
                        v_isShared_6617_ = v_isSharedCheck_6624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6614_);
                        lean_inc(v_head_6613_);
                        lean_dec(v_x_6612_);
                        v___x_6616_ = lean_box(0);
                        v_isShared_6617_ = v_isSharedCheck_6624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6610_);
                if v_isShared_6617_ == 0 {
                    lean_ctor_set_tag(v___x_6616_, 5);
                    lean_ctor_set(v___x_6616_, 1, v_x_6610_);
                    lean_ctor_set(v___x_6616_, 0, v_x_6611_);
                    v___x_6619_ = v___x_6616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6623_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_x_6611_);
                    lean_ctor_set(v_reuseFailAlloc_6623_, 1, v_x_6610_);
                    v___x_6619_ = v_reuseFailAlloc_6623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6620_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_6613_);
                v___x_6621_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6621_, 0, v___x_6619_);
                lean_ctor_set(v___x_6621_, 1, v___x_6620_);
                v_x_6611_ = v___x_6621_;
                v_x_6612_ = v_tail_6614_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(
    mut v_x_6625_: *mut LeanObject,
    mut v_x_6626_: *mut LeanObject,
    mut v_x_6627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6632_: u8 = 0;
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6627_) == 0 {
                    lean_dec(v_x_6625_);
                    return v_x_6626_;
                } else {
                    v_head_6628_ = lean_ctor_get(v_x_6627_, 0);
                    v_tail_6629_ = lean_ctor_get(v_x_6627_, 1);
                    v_isSharedCheck_6639_ = (!lean_is_exclusive(v_x_6627_)) as u8;
                    if v_isSharedCheck_6639_ == 0 {
                        v___x_6631_ = v_x_6627_;
                        v_isShared_6632_ = v_isSharedCheck_6639_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6629_);
                        lean_inc(v_head_6628_);
                        lean_dec(v_x_6627_);
                        v___x_6631_ = lean_box(0);
                        v_isShared_6632_ = v_isSharedCheck_6639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_6625_);
                if v_isShared_6632_ == 0 {
                    lean_ctor_set_tag(v___x_6631_, 5);
                    lean_ctor_set(v___x_6631_, 1, v_x_6625_);
                    lean_ctor_set(v___x_6631_, 0, v_x_6626_);
                    v___x_6634_ = v___x_6631_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6638_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_x_6626_);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 1, v_x_6625_);
                    v___x_6634_ = v_reuseFailAlloc_6638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6635_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_6628_);
                v___x_6636_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6636_, 0, v___x_6634_);
                lean_ctor_set(v___x_6636_, 1, v___x_6635_);
                v___x_6637_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(v_x_6625_, v___x_6636_, v_tail_6629_);
                return v___x_6637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(
    mut v_x_6640_: *mut LeanObject,
    mut v_x_6641_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6640_) == 0 {
        let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_6641_);
        v___x_6642_ = lean_box(0);
        return v___x_6642_;
    } else {
        let mut v_tail_6643_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6643_ = lean_ctor_get(v_x_6640_, 1);
        if lean_obj_tag(v_tail_6643_) == 0 {
            let mut v_head_6644_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_6641_);
            v_head_6644_ = lean_ctor_get(v_x_6640_, 0);
            lean_inc(v_head_6644_);
            lean_dec_ref_known(v_x_6640_, 2);
            v___x_6645_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_6644_);
            return v___x_6645_;
        } else {
            let mut v_head_6646_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_6643_);
            v_head_6646_ = lean_ctor_get(v_x_6640_, 0);
            lean_inc(v_head_6646_);
            lean_dec_ref_known(v_x_6640_, 2);
            v___x_6647_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_6646_);
            v___x_6648_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(v_x_6641_, v___x_6647_, v_tail_6643_);
            return v___x_6648_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    v___x_6653_ =
        l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2;
    v___x_6654_ = lean_string_length(v___x_6653_);
    return v___x_6654_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    v___x_6655_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once), _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
    v___x_6656_ = lean_nat_to_int(v___x_6655_);
    return v___x_6656_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(
    mut v_a_6659_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_6659_) == 0 {
        let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
        v___x_6660_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1;
        return v___x_6660_;
    } else {
        let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6669_: u8 = 0;
        let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
        v___x_6661_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1;
        v___x_6662_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_6659_, v___x_6661_);
        v___x_6663_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once), _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
        v___x_6664_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5;
        v___x_6665_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_6665_, 0, v___x_6664_);
        lean_ctor_set(v___x_6665_, 1, v___x_6662_);
        v___x_6666_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6;
        v___x_6667_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_6667_, 0, v___x_6665_);
        lean_ctor_set(v___x_6667_, 1, v___x_6666_);
        v___x_6668_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_6668_, 0, v___x_6663_);
        lean_ctor_set(v___x_6668_, 1, v___x_6667_);
        v___x_6669_ = 0;
        v___x_6670_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_6670_, 0, v___x_6668_);
        lean_ctor_set_uint8(
            v___x_6670_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_6669_,
        );
        return v___x_6670_;
    }
}
pub unsafe fn _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    v___x_6680_ = lean_unsigned_to_nat(7);
    v___x_6681_ = lean_nat_to_int(v___x_6680_);
    return v___x_6681_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminators_repr___redArg(
    mut v_x_6685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: u8 = 0;
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    v___x_6686_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3;
    v___x_6687_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4,
    );
    v___x_6688_ = lean_unsigned_to_nat(0);
    v___x_6689_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(
            v_x_6685_,
        );
    v___x_6690_ =
        l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_6689_);
    v___x_6691_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6;
    v___x_6692_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6692_, 0, v___x_6690_);
    lean_ctor_set(v___x_6692_, 1, v___x_6691_);
    v___x_6693_ = l_Repr_addAppParen(v___x_6692_, v___x_6688_);
    v___x_6694_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6694_, 0, v___x_6687_);
    lean_ctor_set(v___x_6694_, 1, v___x_6693_);
    v___x_6695_ = 0;
    v___x_6696_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6696_, 0, v___x_6694_);
    lean_ctor_set_uint8(
        v___x_6696_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6695_,
    );
    v___x_6697_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6697_, 0, v___x_6686_);
    lean_ctor_set(v___x_6697_, 1, v___x_6696_);
    v___x_6698_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once),
        _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20,
    );
    v___x_6699_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21;
    v___x_6700_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6700_, 0, v___x_6699_);
    lean_ctor_set(v___x_6700_, 1, v___x_6697_);
    v___x_6701_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22;
    v___x_6702_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6702_, 0, v___x_6700_);
    lean_ctor_set(v___x_6702_, 1, v___x_6701_);
    v___x_6703_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_6703_, 0, v___x_6698_);
    lean_ctor_set(v___x_6703_, 1, v___x_6702_);
    v___x_6704_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_6704_, 0, v___x_6703_);
    lean_ctor_set_uint8(
        v___x_6704_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6695_,
    );
    return v___x_6704_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(
    mut v_x_6705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6706_: *mut LeanObject = core::ptr::null_mut();
    v_res_6706_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_6705_);
    lean_dec_ref(v_x_6705_);
    return v_res_6706_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminators_repr(
    mut v_x_6707_: *mut LeanObject,
    mut v_prec_6708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    v___x_6709_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_6707_);
    return v___x_6709_;
}
pub unsafe fn l_Lean_Meta_instReprCustomEliminators_repr___boxed(
    mut v_x_6710_: *mut LeanObject,
    mut v_prec_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6712_: *mut LeanObject = core::ptr::null_mut();
    v_res_6712_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_6710_, v_prec_6711_);
    lean_dec(v_prec_6711_);
    lean_dec_ref(v_x_6710_);
    return v_res_6712_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(
    mut v_00_u03b2_6713_: *mut LeanObject,
    mut v_m_6714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    v___x_6715_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(
            v_m_6714_,
        );
    return v___x_6715_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(
    mut v_00_u03b2_6716_: *mut LeanObject,
    mut v_m_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6718_: *mut LeanObject = core::ptr::null_mut();
    v_res_6718_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(
        v_00_u03b2_6716_,
        v_m_6717_,
    );
    lean_dec_ref(v_m_6717_);
    return v_res_6718_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(
    mut v_a_6719_: *mut LeanObject,
    mut v_n_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    v___x_6721_ =
        l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_6719_);
    return v___x_6721_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(
    mut v_a_6722_: *mut LeanObject,
    mut v_n_6723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6724_: *mut LeanObject = core::ptr::null_mut();
    v_res_6724_ =
        l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_6722_, v_n_6723_);
    lean_dec(v_n_6723_);
    return v_res_6724_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(
    mut v_00_u03b2_6725_: *mut LeanObject,
    mut v_00_u03c3_6726_: *mut LeanObject,
    mut v_f_6727_: *mut LeanObject,
    mut v_init_6728_: *mut LeanObject,
    mut v_m_6729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6730_: *mut LeanObject = core::ptr::null_mut();
    v___x_6730_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_6727_, v_init_6728_, v_m_6729_);
    return v___x_6730_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(
    mut v_00_u03b2_6731_: *mut LeanObject,
    mut v_00_u03c3_6732_: *mut LeanObject,
    mut v_f_6733_: *mut LeanObject,
    mut v_init_6734_: *mut LeanObject,
    mut v_m_6735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6736_: *mut LeanObject = core::ptr::null_mut();
    v_res_6736_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_6731_, v_00_u03c3_6732_, v_f_6733_, v_init_6734_, v_m_6735_);
    lean_dec_ref(v_m_6735_);
    return v_res_6736_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(
    mut v_x_6737_: *mut LeanObject,
    mut v_x_6738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    v___x_6739_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_6737_);
    return v___x_6739_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(
    mut v_x_6740_: *mut LeanObject,
    mut v_x_6741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6742_: *mut LeanObject = core::ptr::null_mut();
    v_res_6742_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_6740_, v_x_6741_);
    lean_dec(v_x_6741_);
    return v_res_6742_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6743_: *mut LeanObject,
    mut v_00_u03c3_6744_: *mut LeanObject,
    mut v_f_6745_: *mut LeanObject,
    mut v_x_6746_: *mut LeanObject,
    mut v_x_6747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    v___x_6748_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_6745_, v_x_6746_, v_x_6747_);
    return v___x_6748_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(
    mut v_00_u03c3_6749_: *mut LeanObject,
    mut v_00_u03b2_6750_: *mut LeanObject,
    mut v_map_6751_: *mut LeanObject,
    mut v_f_6752_: *mut LeanObject,
    mut v_init_6753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    v___x_6754_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_6751_, v_f_6752_, v_init_6753_);
    return v___x_6754_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03c3_6755_: *mut LeanObject,
    mut v_00_u03b2_6756_: *mut LeanObject,
    mut v_map_6757_: *mut LeanObject,
    mut v_f_6758_: *mut LeanObject,
    mut v_init_6759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6760_: *mut LeanObject = core::ptr::null_mut();
    v_res_6760_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_6755_, v_00_u03b2_6756_, v_map_6757_, v_f_6758_, v_init_6759_);
    lean_dec_ref(v_map_6757_);
    return v_res_6760_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(
    mut v_00_u03b2_6761_: *mut LeanObject,
    mut v_00_u03c3_6762_: *mut LeanObject,
    mut v_f_6763_: *mut LeanObject,
    mut v_as_6764_: *mut LeanObject,
    mut v_i_6765_: usize,
    mut v_stop_6766_: usize,
    mut v_b_6767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    v___x_6768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_6763_, v_as_6764_, v_i_6765_, v_stop_6766_, v_b_6767_);
    return v___x_6768_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_6769_: *mut LeanObject,
    mut v_00_u03c3_6770_: *mut LeanObject,
    mut v_f_6771_: *mut LeanObject,
    mut v_as_6772_: *mut LeanObject,
    mut v_i_6773_: *mut LeanObject,
    mut v_stop_6774_: *mut LeanObject,
    mut v_b_6775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6776_: usize = 0;
    let mut v_stop_boxed_6777_: usize = 0;
    let mut v_res_6778_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6776_ = lean_unbox_usize(v_i_6773_);
    lean_dec(v_i_6773_);
    v_stop_boxed_6777_ = lean_unbox_usize(v_stop_6774_);
    lean_dec(v_stop_6774_);
    v_res_6778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(v_00_u03b2_6769_, v_00_u03c3_6770_, v_f_6771_, v_as_6772_, v_i_boxed_6776_, v_stop_boxed_6777_, v_b_6775_);
    lean_dec_ref(v_as_6772_);
    return v_res_6778_;
}
pub unsafe fn l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(
    mut v_x_6779_: *mut LeanObject,
    mut v_x_6780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    v___x_6781_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_x_6779_);
    return v___x_6781_;
}
pub unsafe fn l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(
    mut v_x_6782_: *mut LeanObject,
    mut v_x_6783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6784_: *mut LeanObject = core::ptr::null_mut();
    v_res_6784_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v_x_6782_, v_x_6783_);
    lean_dec(v_x_6783_);
    return v_res_6784_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_map_6785_: *mut LeanObject,
    mut v_f_6786_: *mut LeanObject,
    mut v_init_6787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    v___x_6788_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_6786_, v_map_6785_, v_init_6787_);
    return v___x_6788_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_map_6789_: *mut LeanObject,
    mut v_f_6790_: *mut LeanObject,
    mut v_init_6791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6792_: *mut LeanObject = core::ptr::null_mut();
    v_res_6792_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_6789_, v_f_6790_, v_init_6791_);
    lean_dec_ref(v_map_6789_);
    return v_res_6792_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03c3_6793_: *mut LeanObject,
    mut v_00_u03b2_6794_: *mut LeanObject,
    mut v_map_6795_: *mut LeanObject,
    mut v_f_6796_: *mut LeanObject,
    mut v_init_6797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    v___x_6798_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_6796_, v_map_6795_, v_init_6797_);
    return v___x_6798_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03c3_6799_: *mut LeanObject,
    mut v_00_u03b2_6800_: *mut LeanObject,
    mut v_map_6801_: *mut LeanObject,
    mut v_f_6802_: *mut LeanObject,
    mut v_init_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6804_: *mut LeanObject = core::ptr::null_mut();
    v_res_6804_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_6799_, v_00_u03b2_6800_, v_map_6801_, v_f_6802_, v_init_6803_);
    lean_dec_ref(v_map_6801_);
    return v_res_6804_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(
    mut v_00_u03c3_6805_: *mut LeanObject,
    mut v_00_u03b1_6806_: *mut LeanObject,
    mut v_00_u03b2_6807_: *mut LeanObject,
    mut v_f_6808_: *mut LeanObject,
    mut v_x_6809_: *mut LeanObject,
    mut v_x_6810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    v___x_6811_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_6808_, v_x_6809_, v_x_6810_);
    return v___x_6811_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03c3_6812_: *mut LeanObject,
    mut v_00_u03b1_6813_: *mut LeanObject,
    mut v_00_u03b2_6814_: *mut LeanObject,
    mut v_f_6815_: *mut LeanObject,
    mut v_x_6816_: *mut LeanObject,
    mut v_x_6817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6818_: *mut LeanObject = core::ptr::null_mut();
    v_res_6818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_6812_, v_00_u03b1_6813_, v_00_u03b2_6814_, v_f_6815_, v_x_6816_, v_x_6817_);
    lean_dec_ref(v_x_6816_);
    return v_res_6818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(
    mut v_00_u03b1_6819_: *mut LeanObject,
    mut v_00_u03b2_6820_: *mut LeanObject,
    mut v_00_u03c3_6821_: *mut LeanObject,
    mut v_f_6822_: *mut LeanObject,
    mut v_as_6823_: *mut LeanObject,
    mut v_i_6824_: usize,
    mut v_stop_6825_: usize,
    mut v_b_6826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    v___x_6827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_6822_, v_as_6823_, v_i_6824_, v_stop_6825_, v_b_6826_);
    return v___x_6827_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(
    mut v_00_u03b1_6828_: *mut LeanObject,
    mut v_00_u03b2_6829_: *mut LeanObject,
    mut v_00_u03c3_6830_: *mut LeanObject,
    mut v_f_6831_: *mut LeanObject,
    mut v_as_6832_: *mut LeanObject,
    mut v_i_6833_: *mut LeanObject,
    mut v_stop_6834_: *mut LeanObject,
    mut v_b_6835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6836_: usize = 0;
    let mut v_stop_boxed_6837_: usize = 0;
    let mut v_res_6838_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6836_ = lean_unbox_usize(v_i_6833_);
    lean_dec(v_i_6833_);
    v_stop_boxed_6837_ = lean_unbox_usize(v_stop_6834_);
    lean_dec(v_stop_6834_);
    v_res_6838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_6828_, v_00_u03b2_6829_, v_00_u03c3_6830_, v_f_6831_, v_as_6832_, v_i_boxed_6836_, v_stop_boxed_6837_, v_b_6835_);
    lean_dec_ref(v_as_6832_);
    return v_res_6838_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(
    mut v_00_u03c3_6839_: *mut LeanObject,
    mut v_00_u03b1_6840_: *mut LeanObject,
    mut v_00_u03b2_6841_: *mut LeanObject,
    mut v_f_6842_: *mut LeanObject,
    mut v_keys_6843_: *mut LeanObject,
    mut v_vals_6844_: *mut LeanObject,
    mut v_heq_6845_: *mut LeanObject,
    mut v_i_6846_: *mut LeanObject,
    mut v_acc_6847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    v___x_6848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_6842_, v_keys_6843_, v_vals_6844_, v_i_6846_, v_acc_6847_);
    return v___x_6848_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(
    mut v_00_u03c3_6849_: *mut LeanObject,
    mut v_00_u03b1_6850_: *mut LeanObject,
    mut v_00_u03b2_6851_: *mut LeanObject,
    mut v_f_6852_: *mut LeanObject,
    mut v_keys_6853_: *mut LeanObject,
    mut v_vals_6854_: *mut LeanObject,
    mut v_heq_6855_: *mut LeanObject,
    mut v_i_6856_: *mut LeanObject,
    mut v_acc_6857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6858_: *mut LeanObject = core::ptr::null_mut();
    v_res_6858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_6849_, v_00_u03b1_6850_, v_00_u03b2_6851_, v_f_6852_, v_keys_6853_, v_vals_6854_, v_heq_6855_, v_i_6856_, v_acc_6857_);
    lean_dec_ref(v_vals_6854_);
    lean_dec_ref(v_keys_6853_);
    return v_res_6858_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0()
-> u64 {
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: u64 = 0;
    v___x_6861_ = lean_unsigned_to_nat(1723);
    v___x_6862_ = lean_uint64_of_nat(v___x_6861_);
    return v___x_6862_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(
    mut v_as_6863_: *mut LeanObject,
    mut v_i_6864_: usize,
    mut v_stop_6865_: usize,
    mut v_b_6866_: u64,
) -> u64 {
    let mut v___y_6868_: u64 = 0;
    let mut v___x_6869_: u64 = 0;
    let mut v___x_6870_: usize = 0;
    let mut v___x_6871_: usize = 0;
    let mut v___x_6873_: u8 = 0;
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: u64 = 0;
    let mut v_hash_6876_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6873_ = lean_usize_dec_eq(v_i_6864_, v_stop_6865_);
                if v___x_6873_ == 0 {
                    v___x_6874_ = lean_array_uget_borrowed(v_as_6863_, v_i_6864_);
                    if lean_obj_tag(v___x_6874_) == 0 {
                        v___x_6875_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0);
                        v___y_6868_ = v___x_6875_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_6876_ = lean_ctor_get_uint64(
                            v___x_6874_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_6868_ = v_hash_6876_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6866_;
                }
            }
            1 => {
                v___x_6869_ = lean_uint64_mix_hash(v_b_6866_, v___y_6868_);
                v___x_6870_ = 1usize;
                v___x_6871_ = lean_usize_add(v_i_6864_, v___x_6870_);
                v_i_6864_ = v___x_6871_;
                v_b_6866_ = v___x_6869_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(
    mut v_as_6877_: *mut LeanObject,
    mut v_i_6878_: *mut LeanObject,
    mut v_stop_6879_: *mut LeanObject,
    mut v_b_6880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6881_: usize = 0;
    let mut v_stop_boxed_6882_: usize = 0;
    let mut v_b_boxed_6883_: u64 = 0;
    let mut v_res_6884_: u64 = 0;
    let mut v_r_6885_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6881_ = lean_unbox_usize(v_i_6878_);
    lean_dec(v_i_6878_);
    v_stop_boxed_6882_ = lean_unbox_usize(v_stop_6879_);
    lean_dec(v_stop_6879_);
    v_b_boxed_6883_ = lean_unbox_uint64(v_b_6880_);
    lean_dec_ref(v_b_6880_);
    v_res_6884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_6877_, v_i_boxed_6881_, v_stop_boxed_6882_, v_b_boxed_6883_);
    lean_dec_ref(v_as_6877_);
    v_r_6885_ = lean_box_uint64(v_res_6884_);
    return v_r_6885_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(
    mut v_x_6886_: *mut LeanObject,
    mut v_x_6887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v_fst_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: u64 = 0;
    let mut v___y_6899_: u64 = 0;
    let mut v___x_6900_: u64 = 0;
    let mut v___x_6901_: u64 = 0;
    let mut v___x_6902_: u64 = 0;
    let mut v_fold_6903_: u64 = 0;
    let mut v___x_6904_: u64 = 0;
    let mut v___x_6905_: u64 = 0;
    let mut v___x_6906_: u64 = 0;
    let mut v___x_6907_: usize = 0;
    let mut v___x_6908_: usize = 0;
    let mut v___x_6909_: usize = 0;
    let mut v___x_6910_: usize = 0;
    let mut v___x_6911_: usize = 0;
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6919_: u64 = 0;
    let mut v___x_6920_: u64 = 0;
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: u8 = 0;
    let mut v___x_6924_: u8 = 0;
    let mut v___x_6925_: usize = 0;
    let mut v___x_6926_: usize = 0;
    let mut v___x_6927_: u64 = 0;
    let mut v___x_6928_: usize = 0;
    let mut v___x_6929_: usize = 0;
    let mut v___x_6930_: u64 = 0;
    let mut v___x_6931_: u8 = 0;
    let mut v___x_6932_: u64 = 0;
    let mut v___x_6933_: u64 = 0;
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6887_) == 0 {
                    return v_x_6886_;
                } else {
                    v_key_6888_ = lean_ctor_get(v_x_6887_, 0);
                    v_value_6889_ = lean_ctor_get(v_x_6887_, 1);
                    v_tail_6890_ = lean_ctor_get(v_x_6887_, 2);
                    v_isSharedCheck_6934_ = (!lean_is_exclusive(v_x_6887_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6892_ = v_x_6887_;
                        v_isShared_6893_ = v_isSharedCheck_6934_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6890_);
                        lean_inc(v_value_6889_);
                        lean_inc(v_key_6888_);
                        lean_dec(v_x_6887_);
                        v___x_6892_ = lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6934_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6894_ = lean_ctor_get(v_key_6888_, 0);
                v_snd_6895_ = lean_ctor_get(v_key_6888_, 1);
                v___x_6896_ = lean_array_get_size(v_x_6886_);
                v___x_6931_ = (lean_unbox(v_fst_6894_) as u8);
                if v___x_6931_ == 0 {
                    v___x_6932_ = 13u64;
                    v___y_6919_ = v___x_6932_;
                    state = 4;
                    continue;
                } else {
                    v___x_6933_ = 11u64;
                    v___y_6919_ = v___x_6933_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_6900_ = lean_uint64_mix_hash(v___y_6898_, v___y_6899_);
                v___x_6901_ = 32u64;
                v___x_6902_ = lean_uint64_shift_right(v___x_6900_, v___x_6901_);
                v_fold_6903_ = lean_uint64_xor(v___x_6900_, v___x_6902_);
                v___x_6904_ = 16u64;
                v___x_6905_ = lean_uint64_shift_right(v_fold_6903_, v___x_6904_);
                v___x_6906_ = lean_uint64_xor(v_fold_6903_, v___x_6905_);
                v___x_6907_ = lean_uint64_to_usize(v___x_6906_);
                v___x_6908_ = lean_usize_of_nat(v___x_6896_);
                v___x_6909_ = 1usize;
                v___x_6910_ = lean_usize_sub(v___x_6908_, v___x_6909_);
                v___x_6911_ = lean_usize_land(v___x_6907_, v___x_6910_);
                v___x_6912_ = lean_array_uget_borrowed(v_x_6886_, v___x_6911_);
                lean_inc(v___x_6912_);
                if v_isShared_6893_ == 0 {
                    lean_ctor_set(v___x_6892_, 2, v___x_6912_);
                    v___x_6914_ = v___x_6892_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6917_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6917_, 0, v_key_6888_);
                    lean_ctor_set(v_reuseFailAlloc_6917_, 1, v_value_6889_);
                    lean_ctor_set(v_reuseFailAlloc_6917_, 2, v___x_6912_);
                    v___x_6914_ = v_reuseFailAlloc_6917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6915_ = lean_array_uset(v_x_6886_, v___x_6911_, v___x_6914_);
                v_x_6886_ = v___x_6915_;
                v_x_6887_ = v_tail_6890_;
                state = 0;
                continue;
            }
            4 => {
                v___x_6920_ = 7u64;
                v___x_6921_ = lean_unsigned_to_nat(0);
                v___x_6922_ = lean_array_get_size(v_snd_6895_);
                v___x_6923_ = lean_nat_dec_lt(v___x_6921_, v___x_6922_);
                if v___x_6923_ == 0 {
                    v___y_6898_ = v___y_6919_;
                    v___y_6899_ = v___x_6920_;
                    state = 2;
                    continue;
                } else {
                    v___x_6924_ = lean_nat_dec_le(v___x_6922_, v___x_6922_);
                    if v___x_6924_ == 0 {
                        if v___x_6923_ == 0 {
                            v___y_6898_ = v___y_6919_;
                            v___y_6899_ = v___x_6920_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6925_ = 0usize;
                            v___x_6926_ = lean_usize_of_nat(v___x_6922_);
                            v___x_6927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_6895_, v___x_6925_, v___x_6926_, v___x_6920_);
                            v___y_6898_ = v___y_6919_;
                            v___y_6899_ = v___x_6927_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_6928_ = 0usize;
                        v___x_6929_ = lean_usize_of_nat(v___x_6922_);
                        v___x_6930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_6895_, v___x_6928_, v___x_6929_, v___x_6920_);
                        v___y_6898_ = v___y_6919_;
                        v___y_6899_ = v___x_6930_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(
    mut v_i_6935_: *mut LeanObject,
    mut v_source_6936_: *mut LeanObject,
    mut v_target_6937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: u8 = 0;
    let mut v_es_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6938_ = lean_array_get_size(v_source_6936_);
                v___x_6939_ = lean_nat_dec_lt(v_i_6935_, v___x_6938_);
                if v___x_6939_ == 0 {
                    lean_dec_ref(v_source_6936_);
                    lean_dec(v_i_6935_);
                    return v_target_6937_;
                } else {
                    v_es_6940_ = lean_array_fget(v_source_6936_, v_i_6935_);
                    v___x_6941_ = lean_box(0);
                    v_source_6942_ = lean_array_fset(v_source_6936_, v_i_6935_, v___x_6941_);
                    v_target_6943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_target_6937_, v_es_6940_);
                    v___x_6944_ = lean_unsigned_to_nat(1);
                    v___x_6945_ = lean_nat_add(v_i_6935_, v___x_6944_);
                    lean_dec(v_i_6935_);
                    v_i_6935_ = v___x_6945_;
                    v_source_6936_ = v_source_6942_;
                    v_target_6937_ = v_target_6943_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(
    mut v_data_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    v___x_6948_ = lean_array_get_size(v_data_6947_);
    v___x_6949_ = lean_unsigned_to_nat(2);
    v_nbuckets_6950_ = lean_nat_mul(v___x_6948_, v___x_6949_);
    v___x_6951_ = lean_unsigned_to_nat(0);
    v___x_6952_ = lean_box(0);
    v___x_6953_ = lean_mk_array(v_nbuckets_6950_, v___x_6952_);
    v___x_6954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v___x_6951_, v_data_6947_, v___x_6953_);
    return v___x_6954_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_xs_6955_: *mut LeanObject,
    mut v_ys_6956_: *mut LeanObject,
    mut v_x_6957_: *mut LeanObject,
) -> u8 {
    let mut v_zero_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6959_: u8 = 0;
    let mut v_one_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6958_ = lean_unsigned_to_nat(0);
                v_isZero_6959_ = lean_nat_dec_eq(v_x_6957_, v_zero_6958_);
                if v_isZero_6959_ == 1 {
                    lean_dec(v_x_6957_);
                    return v_isZero_6959_;
                } else {
                    v_one_6960_ = lean_unsigned_to_nat(1);
                    v_n_6961_ = lean_nat_sub(v_x_6957_, v_one_6960_);
                    lean_dec(v_x_6957_);
                    v___x_6962_ = lean_array_fget_borrowed(v_xs_6955_, v_n_6961_);
                    v___x_6963_ = lean_array_fget_borrowed(v_ys_6956_, v_n_6961_);
                    v___x_6964_ = lean_name_eq(v___x_6962_, v___x_6963_);
                    if v___x_6964_ == 0 {
                        lean_dec(v_n_6961_);
                        return v___x_6964_;
                    } else {
                        v_x_6957_ = v_n_6961_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_xs_6966_: *mut LeanObject,
    mut v_ys_6967_: *mut LeanObject,
    mut v_x_6968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6969_: u8 = 0;
    let mut v_r_6970_: *mut LeanObject = core::ptr::null_mut();
    v_res_6969_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_6966_, v_ys_6967_, v_x_6968_);
    lean_dec_ref(v_ys_6967_);
    lean_dec_ref(v_xs_6966_);
    v_r_6970_ = lean_box((v_res_6969_) as usize);
    return v_r_6970_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(
    mut v_a_6971_: *mut LeanObject,
    mut v_b_6972_: *mut LeanObject,
    mut v_x_6973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6979_: u8 = 0;
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: u8 = 0;
    let mut v___x_6993_: u8 = 0;
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: u8 = 0;
    let mut v___x_6996_: u8 = 0;
    let mut v___x_6997_: u8 = 0;
    let mut v_isSharedCheck_6998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6973_) == 0 {
                    lean_dec(v_b_6972_);
                    lean_dec_ref(v_a_6971_);
                    return v_x_6973_;
                } else {
                    v_key_6974_ = lean_ctor_get(v_x_6973_, 0);
                    v_value_6975_ = lean_ctor_get(v_x_6973_, 1);
                    v_tail_6976_ = lean_ctor_get(v_x_6973_, 2);
                    v_isSharedCheck_6998_ = (!lean_is_exclusive(v_x_6973_)) as u8;
                    if v_isSharedCheck_6998_ == 0 {
                        v___x_6978_ = v_x_6973_;
                        v_isShared_6979_ = v_isSharedCheck_6998_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6976_);
                        lean_inc(v_value_6975_);
                        lean_inc(v_key_6974_);
                        lean_dec(v_x_6973_);
                        v___x_6978_ = lean_box(0);
                        v_isShared_6979_ = v_isSharedCheck_6998_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6985_ = lean_ctor_get(v_key_6974_, 0);
                v_snd_6986_ = lean_ctor_get(v_key_6974_, 1);
                v_fst_6987_ = lean_ctor_get(v_a_6971_, 0);
                v_snd_6988_ = lean_ctor_get(v_a_6971_, 1);
                v___x_6995_ = (lean_unbox(v_fst_6985_) as u8);
                if v___x_6995_ == 0 {
                    v___x_6996_ = (lean_unbox(v_fst_6987_) as u8);
                    if v___x_6996_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6997_ = (lean_unbox(v_fst_6987_) as u8);
                    if v___x_6997_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6981_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_6971_, v_b_6972_, v_tail_6976_);
                if v_isShared_6979_ == 0 {
                    lean_ctor_set(v___x_6978_, 2, v___x_6981_);
                    v___x_6983_ = v___x_6978_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6984_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_key_6974_);
                    lean_ctor_set(v_reuseFailAlloc_6984_, 1, v_value_6975_);
                    lean_ctor_set(v_reuseFailAlloc_6984_, 2, v___x_6981_);
                    v___x_6983_ = v_reuseFailAlloc_6984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6983_;
            }
            4 => {
                v___x_6990_ = lean_array_get_size(v_snd_6986_);
                v___x_6991_ = lean_array_get_size(v_snd_6988_);
                v___x_6992_ = lean_nat_dec_eq(v___x_6990_, v___x_6991_);
                if v___x_6992_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_6993_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_6986_, v_snd_6988_, v___x_6990_);
                    if v___x_6993_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_6978_);
                        lean_dec(v_value_6975_);
                        lean_dec(v_key_6974_);
                        v___x_6994_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_6994_, 0, v_a_6971_);
                        lean_ctor_set(v___x_6994_, 1, v_b_6972_);
                        lean_ctor_set(v___x_6994_, 2, v_tail_6976_);
                        return v___x_6994_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(
    mut v_a_6999_: *mut LeanObject,
    mut v_x_7000_: *mut LeanObject,
) -> u8 {
    let mut v___x_7001_: u8 = 0;
    let mut v_key_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7013_: u8 = 0;
    let mut v___x_7015_: u8 = 0;
    let mut v___x_7016_: u8 = 0;
    let mut v___x_7018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7000_) == 0 {
                    v___x_7001_ = 0;
                    return v___x_7001_;
                } else {
                    v_key_7002_ = lean_ctor_get(v_x_7000_, 0);
                    v_tail_7003_ = lean_ctor_get(v_x_7000_, 2);
                    v_fst_7004_ = lean_ctor_get(v_key_7002_, 0);
                    v_snd_7005_ = lean_ctor_get(v_key_7002_, 1);
                    v_fst_7006_ = lean_ctor_get(v_a_6999_, 0);
                    v_snd_7007_ = lean_ctor_get(v_a_6999_, 1);
                    v___x_7015_ = (lean_unbox(v_fst_7004_) as u8);
                    if v___x_7015_ == 0 {
                        v___x_7016_ = (lean_unbox(v_fst_7006_) as u8);
                        if v___x_7016_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_7000_ = v_tail_7003_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_7018_ = (lean_unbox(v_fst_7006_) as u8);
                        if v___x_7018_ == 0 {
                            v_x_7000_ = v_tail_7003_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7009_ = lean_array_get_size(v_snd_7005_);
                v___x_7010_ = lean_array_get_size(v_snd_7007_);
                v___x_7011_ = lean_nat_dec_eq(v___x_7009_, v___x_7010_);
                if v___x_7011_ == 0 {
                    v_x_7000_ = v_tail_7003_;
                    state = 0;
                    continue;
                } else {
                    v___x_7013_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_7005_, v_snd_7007_, v___x_7009_);
                    if v___x_7013_ == 0 {
                        v_x_7000_ = v_tail_7003_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7013_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_a_7020_: *mut LeanObject,
    mut v_x_7021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7022_: u8 = 0;
    let mut v_r_7023_: *mut LeanObject = core::ptr::null_mut();
    v_res_7022_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_7020_, v_x_7021_);
    lean_dec(v_x_7021_);
    lean_dec_ref(v_a_7020_);
    v_r_7023_ = lean_box((v_res_7022_) as usize);
    return v_r_7023_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(
    mut v_m_7024_: *mut LeanObject,
    mut v_a_7025_: *mut LeanObject,
    mut v_b_7026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v_fst_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: u64 = 0;
    let mut v___y_7037_: u64 = 0;
    let mut v___x_7038_: u64 = 0;
    let mut v___x_7039_: u64 = 0;
    let mut v___x_7040_: u64 = 0;
    let mut v_fold_7041_: u64 = 0;
    let mut v___x_7042_: u64 = 0;
    let mut v___x_7043_: u64 = 0;
    let mut v___x_7044_: u64 = 0;
    let mut v___x_7045_: usize = 0;
    let mut v___x_7046_: usize = 0;
    let mut v___x_7047_: usize = 0;
    let mut v___x_7048_: usize = 0;
    let mut v___x_7049_: usize = 0;
    let mut v_bkt_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: u8 = 0;
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: u8 = 0;
    let mut v_val_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7077_: u64 = 0;
    let mut v___x_7078_: u64 = 0;
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: u8 = 0;
    let mut v___x_7082_: u8 = 0;
    let mut v___x_7083_: usize = 0;
    let mut v___x_7084_: usize = 0;
    let mut v___x_7085_: u64 = 0;
    let mut v___x_7086_: usize = 0;
    let mut v___x_7087_: usize = 0;
    let mut v___x_7088_: u64 = 0;
    let mut v___x_7089_: u8 = 0;
    let mut v___x_7090_: u64 = 0;
    let mut v___x_7091_: u64 = 0;
    let mut v_isSharedCheck_7092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7027_ = lean_ctor_get(v_m_7024_, 0);
                v_buckets_7028_ = lean_ctor_get(v_m_7024_, 1);
                v_isSharedCheck_7092_ = (!lean_is_exclusive(v_m_7024_)) as u8;
                if v_isSharedCheck_7092_ == 0 {
                    v___x_7030_ = v_m_7024_;
                    v_isShared_7031_ = v_isSharedCheck_7092_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_7028_);
                    lean_inc(v_size_7027_);
                    lean_dec(v_m_7024_);
                    v___x_7030_ = lean_box(0);
                    v_isShared_7031_ = v_isSharedCheck_7092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_7032_ = lean_ctor_get(v_a_7025_, 0);
                v_snd_7033_ = lean_ctor_get(v_a_7025_, 1);
                v___x_7034_ = lean_array_get_size(v_buckets_7028_);
                v___x_7089_ = (lean_unbox(v_fst_7032_) as u8);
                if v___x_7089_ == 0 {
                    v___x_7090_ = 13u64;
                    v___y_7077_ = v___x_7090_;
                    state = 6;
                    continue;
                } else {
                    v___x_7091_ = 11u64;
                    v___y_7077_ = v___x_7091_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v___x_7038_ = lean_uint64_mix_hash(v___y_7036_, v___y_7037_);
                v___x_7039_ = 32u64;
                v___x_7040_ = lean_uint64_shift_right(v___x_7038_, v___x_7039_);
                v_fold_7041_ = lean_uint64_xor(v___x_7038_, v___x_7040_);
                v___x_7042_ = 16u64;
                v___x_7043_ = lean_uint64_shift_right(v_fold_7041_, v___x_7042_);
                v___x_7044_ = lean_uint64_xor(v_fold_7041_, v___x_7043_);
                v___x_7045_ = lean_uint64_to_usize(v___x_7044_);
                v___x_7046_ = lean_usize_of_nat(v___x_7034_);
                v___x_7047_ = 1usize;
                v___x_7048_ = lean_usize_sub(v___x_7046_, v___x_7047_);
                v___x_7049_ = lean_usize_land(v___x_7045_, v___x_7048_);
                v_bkt_7050_ = lean_array_uget_borrowed(v_buckets_7028_, v___x_7049_);
                v___x_7051_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_7025_, v_bkt_7050_);
                if v___x_7051_ == 0 {
                    v___x_7052_ = lean_unsigned_to_nat(1);
                    v_size_x27_7053_ = lean_nat_add(v_size_7027_, v___x_7052_);
                    lean_dec(v_size_7027_);
                    lean_inc(v_bkt_7050_);
                    v___x_7054_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_7054_, 0, v_a_7025_);
                    lean_ctor_set(v___x_7054_, 1, v_b_7026_);
                    lean_ctor_set(v___x_7054_, 2, v_bkt_7050_);
                    v_buckets_x27_7055_ =
                        lean_array_uset(v_buckets_7028_, v___x_7049_, v___x_7054_);
                    v___x_7056_ = lean_unsigned_to_nat(4);
                    v___x_7057_ = lean_nat_mul(v_size_x27_7053_, v___x_7056_);
                    v___x_7058_ = lean_unsigned_to_nat(3);
                    v___x_7059_ = lean_nat_div(v___x_7057_, v___x_7058_);
                    lean_dec(v___x_7057_);
                    v___x_7060_ = lean_array_get_size(v_buckets_x27_7055_);
                    v___x_7061_ = lean_nat_dec_le(v___x_7059_, v___x_7060_);
                    lean_dec(v___x_7059_);
                    if v___x_7061_ == 0 {
                        v_val_7062_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_buckets_x27_7055_);
                        if v_isShared_7031_ == 0 {
                            lean_ctor_set(v___x_7030_, 1, v_val_7062_);
                            lean_ctor_set(v___x_7030_, 0, v_size_x27_7053_);
                            v___x_7064_ = v___x_7030_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7065_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7065_, 0, v_size_x27_7053_);
                            lean_ctor_set(v_reuseFailAlloc_7065_, 1, v_val_7062_);
                            v___x_7064_ = v_reuseFailAlloc_7065_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_7031_ == 0 {
                            lean_ctor_set(v___x_7030_, 1, v_buckets_x27_7055_);
                            lean_ctor_set(v___x_7030_, 0, v_size_x27_7053_);
                            v___x_7067_ = v___x_7030_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7068_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7068_, 0, v_size_x27_7053_);
                            lean_ctor_set(v_reuseFailAlloc_7068_, 1, v_buckets_x27_7055_);
                            v___x_7067_ = v_reuseFailAlloc_7068_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_7050_);
                    v___x_7069_ = lean_box(0);
                    v_buckets_x27_7070_ =
                        lean_array_uset(v_buckets_7028_, v___x_7049_, v___x_7069_);
                    v___x_7071_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_7025_, v_b_7026_, v_bkt_7050_);
                    v___x_7072_ = lean_array_uset(v_buckets_x27_7070_, v___x_7049_, v___x_7071_);
                    if v_isShared_7031_ == 0 {
                        lean_ctor_set(v___x_7030_, 1, v___x_7072_);
                        v___x_7074_ = v___x_7030_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7075_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7075_, 0, v_size_7027_);
                        lean_ctor_set(v_reuseFailAlloc_7075_, 1, v___x_7072_);
                        v___x_7074_ = v_reuseFailAlloc_7075_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7064_;
            }
            4 => {
                return v___x_7067_;
            }
            5 => {
                return v___x_7074_;
            }
            6 => {
                v___x_7078_ = 7u64;
                v___x_7079_ = lean_unsigned_to_nat(0);
                v___x_7080_ = lean_array_get_size(v_snd_7033_);
                v___x_7081_ = lean_nat_dec_lt(v___x_7079_, v___x_7080_);
                if v___x_7081_ == 0 {
                    v___y_7036_ = v___y_7077_;
                    v___y_7037_ = v___x_7078_;
                    state = 2;
                    continue;
                } else {
                    v___x_7082_ = lean_nat_dec_le(v___x_7080_, v___x_7080_);
                    if v___x_7082_ == 0 {
                        if v___x_7081_ == 0 {
                            v___y_7036_ = v___y_7077_;
                            v___y_7037_ = v___x_7078_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7083_ = 0usize;
                            v___x_7084_ = lean_usize_of_nat(v___x_7080_);
                            v___x_7085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7033_, v___x_7083_, v___x_7084_, v___x_7078_);
                            v___y_7036_ = v___y_7077_;
                            v___y_7037_ = v___x_7085_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_7086_ = 0usize;
                        v___x_7087_ = lean_usize_of_nat(v___x_7080_);
                        v___x_7088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7033_, v___x_7086_, v___x_7087_, v___x_7078_);
                        v___y_7036_ = v___y_7077_;
                        v___y_7037_ = v___x_7088_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_x_7093_: *mut LeanObject,
    mut v_x_7094_: *mut LeanObject,
    mut v_x_7095_: *mut LeanObject,
    mut v_x_7096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7101_: u8 = 0;
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: u8 = 0;
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7121_: u8 = 0;
    let mut v___y_7123_: u8 = 0;
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: u8 = 0;
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: u8 = 0;
    let mut v___x_7135_: u8 = 0;
    let mut v_isSharedCheck_7136_: u8 = 0;
    let mut v_isSharedCheck_7137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_7097_ = lean_ctor_get(v_x_7093_, 0);
                v_vs_7098_ = lean_ctor_get(v_x_7093_, 1);
                v_isSharedCheck_7137_ = (!lean_is_exclusive(v_x_7093_)) as u8;
                if v_isSharedCheck_7137_ == 0 {
                    v___x_7100_ = v_x_7093_;
                    v_isShared_7101_ = v_isSharedCheck_7137_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_7098_);
                    lean_inc(v_ks_7097_);
                    lean_dec(v_x_7093_);
                    v___x_7100_ = lean_box(0);
                    v_isShared_7101_ = v_isSharedCheck_7137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7109_ = lean_array_get_size(v_ks_7097_);
                v___x_7110_ = lean_nat_dec_lt(v_x_7094_, v___x_7109_);
                if v___x_7110_ == 0 {
                    lean_del_object(v___x_7100_);
                    lean_dec(v_x_7094_);
                    v___x_7111_ = lean_array_push(v_ks_7097_, v_x_7095_);
                    v___x_7112_ = lean_array_push(v_vs_7098_, v_x_7096_);
                    v___x_7113_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_7113_, 0, v___x_7111_);
                    lean_ctor_set(v___x_7113_, 1, v___x_7112_);
                    return v___x_7113_;
                } else {
                    v_fst_7114_ = lean_ctor_get(v_x_7095_, 0);
                    v_snd_7115_ = lean_ctor_get(v_x_7095_, 1);
                    v_k_x27_7116_ = lean_array_fget(v_ks_7097_, v_x_7094_);
                    v_fst_7117_ = lean_ctor_get(v_k_x27_7116_, 0);
                    v_snd_7118_ = lean_ctor_get(v_k_x27_7116_, 1);
                    v_isSharedCheck_7136_ = (!lean_is_exclusive(v_k_x27_7116_)) as u8;
                    if v_isSharedCheck_7136_ == 0 {
                        v___x_7120_ = v_k_x27_7116_;
                        v_isShared_7121_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_7118_);
                        lean_inc(v_fst_7117_);
                        lean_dec(v_k_x27_7116_);
                        v___x_7120_ = lean_box(0);
                        v_isShared_7121_ = v_isSharedCheck_7136_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7101_ == 0 {
                    v___x_7104_ = v___x_7100_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7108_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_ks_7097_);
                    lean_ctor_set(v_reuseFailAlloc_7108_, 1, v_vs_7098_);
                    v___x_7104_ = v_reuseFailAlloc_7108_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7105_ = lean_unsigned_to_nat(1);
                v___x_7106_ = lean_nat_add(v_x_7094_, v___x_7105_);
                lean_dec(v_x_7094_);
                v_x_7093_ = v___x_7104_;
                v_x_7094_ = v___x_7106_;
                state = 0;
                continue;
            }
            4 => {
                v___x_7133_ = (lean_unbox(v_fst_7114_) as u8);
                if v___x_7133_ == 0 {
                    v___x_7134_ = (lean_unbox(v_fst_7117_) as u8);
                    lean_dec(v_fst_7117_);
                    if v___x_7134_ == 0 {
                        v___y_7123_ = v___x_7110_;
                        state = 5;
                        continue;
                    } else {
                        lean_del_object(v___x_7120_);
                        lean_dec(v_snd_7118_);
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7135_ = (lean_unbox(v_fst_7117_) as u8);
                    lean_dec(v_fst_7117_);
                    v___y_7123_ = v___x_7135_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_7123_ == 0 {
                    lean_del_object(v___x_7120_);
                    lean_dec(v_snd_7118_);
                    state = 2;
                    continue;
                } else {
                    v___x_7124_ = lean_array_get_size(v_snd_7115_);
                    v___x_7125_ = lean_array_get_size(v_snd_7118_);
                    v___x_7126_ = lean_nat_dec_eq(v___x_7124_, v___x_7125_);
                    if v___x_7126_ == 0 {
                        lean_del_object(v___x_7120_);
                        lean_dec(v_snd_7118_);
                        state = 2;
                        continue;
                    } else {
                        v___x_7127_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_7115_, v_snd_7118_, v___x_7124_);
                        lean_dec(v_snd_7118_);
                        if v___x_7127_ == 0 {
                            lean_del_object(v___x_7120_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_7100_);
                            v___x_7128_ = lean_array_fset(v_ks_7097_, v_x_7094_, v_x_7095_);
                            v___x_7129_ = lean_array_fset(v_vs_7098_, v_x_7094_, v_x_7096_);
                            lean_dec(v_x_7094_);
                            if v_isShared_7121_ == 0 {
                                lean_ctor_set_tag(v___x_7120_, 1);
                                lean_ctor_set(v___x_7120_, 1, v___x_7129_);
                                lean_ctor_set(v___x_7120_, 0, v___x_7128_);
                                v___x_7131_ = v___x_7120_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7132_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7132_, 0, v___x_7128_);
                                lean_ctor_set(v_reuseFailAlloc_7132_, 1, v___x_7129_);
                                v___x_7131_ = v_reuseFailAlloc_7132_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                return v___x_7131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_7138_: *mut LeanObject,
    mut v_k_7139_: *mut LeanObject,
    mut v_v_7140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    v___x_7141_ = lean_unsigned_to_nat(0);
    v___x_7142_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_n_7138_, v___x_7141_, v_k_7139_, v_v_7140_);
    return v___x_7142_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    v___x_7143_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_7143_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_7144_: *mut LeanObject,
    mut v_x_7145_: usize,
    mut v_x_7146_: usize,
    mut v_x_7147_: *mut LeanObject,
    mut v_x_7148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: usize = 0;
    let mut v___x_7151_: usize = 0;
    let mut v___x_7152_: usize = 0;
    let mut v___x_7153_: usize = 0;
    let mut v_j_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: u8 = 0;
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v_v_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7173_: u8 = 0;
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7182_: u8 = 0;
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: u8 = 0;
    let mut v___x_7186_: u8 = 0;
    let mut v___x_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: u8 = 0;
    let mut v___x_7191_: u8 = 0;
    let mut v___x_7192_: u8 = 0;
    let mut v_isSharedCheck_7193_: u8 = 0;
    let mut v_node_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7197_: u8 = 0;
    let mut v___x_7198_: usize = 0;
    let mut v___x_7199_: usize = 0;
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7204_: u8 = 0;
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7206_: u8 = 0;
    let mut v_unused_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7212_: u8 = 0;
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7217_: u8 = 0;
    let mut v_ks_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: usize = 0;
    let mut v___x_7224_: u8 = 0;
    let mut v___x_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: u8 = 0;
    let mut v_reuseFailAlloc_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7144_) == 0 {
                    v_es_7149_ = lean_ctor_get(v_x_7144_, 0);
                    v___x_7150_ = 5usize;
                    v___x_7151_ = 1usize;
                    v___x_7152_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_7153_ = lean_usize_land(v_x_7145_, v___x_7152_);
                    v_j_7154_ = lean_usize_to_nat(v___x_7153_);
                    v___x_7155_ = lean_array_get_size(v_es_7149_);
                    v___x_7156_ = lean_nat_dec_lt(v_j_7154_, v___x_7155_);
                    if v___x_7156_ == 0 {
                        lean_dec(v_j_7154_);
                        lean_dec(v_x_7148_);
                        lean_dec_ref(v_x_7147_);
                        return v_x_7144_;
                    } else {
                        lean_inc_ref(v_es_7149_);
                        v_isSharedCheck_7206_ = (!lean_is_exclusive(v_x_7144_)) as u8;
                        if v_isSharedCheck_7206_ == 0 {
                            v_unused_7207_ = lean_ctor_get(v_x_7144_, 0);
                            lean_dec(v_unused_7207_);
                            v___x_7158_ = v_x_7144_;
                            v_isShared_7159_ = v_isSharedCheck_7206_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_7144_);
                            v___x_7158_ = lean_box(0);
                            v_isShared_7159_ = v_isSharedCheck_7206_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_7208_ = lean_ctor_get(v_x_7144_, 0);
                    v_vs_7209_ = lean_ctor_get(v_x_7144_, 1);
                    v_isSharedCheck_7229_ = (!lean_is_exclusive(v_x_7144_)) as u8;
                    if v_isSharedCheck_7229_ == 0 {
                        v___x_7211_ = v_x_7144_;
                        v_isShared_7212_ = v_isSharedCheck_7229_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_vs_7209_);
                        lean_inc(v_ks_7208_);
                        lean_dec(v_x_7144_);
                        v___x_7211_ = lean_box(0);
                        v_isShared_7212_ = v_isSharedCheck_7229_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_v_7160_ = lean_array_fget(v_es_7149_, v_j_7154_);
                v___x_7161_ = lean_box(0);
                v_xs_x27_7162_ = lean_array_fset(v_es_7149_, v_j_7154_, v___x_7161_);
                match lean_obj_tag(v_v_7160_) {
                    0 => {
                        v_key_7169_ = lean_ctor_get(v_v_7160_, 0);
                        v_val_7170_ = lean_ctor_get(v_v_7160_, 1);
                        v_isSharedCheck_7193_ = (!lean_is_exclusive(v_v_7160_)) as u8;
                        if v_isSharedCheck_7193_ == 0 {
                            v___x_7172_ = v_v_7160_;
                            v_isShared_7173_ = v_isSharedCheck_7193_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_7170_);
                            lean_inc(v_key_7169_);
                            lean_dec(v_v_7160_);
                            v___x_7172_ = lean_box(0);
                            v_isShared_7173_ = v_isSharedCheck_7193_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_7194_ = lean_ctor_get(v_v_7160_, 0);
                        v_isSharedCheck_7204_ = (!lean_is_exclusive(v_v_7160_)) as u8;
                        if v_isSharedCheck_7204_ == 0 {
                            v___x_7196_ = v_v_7160_;
                            v_isShared_7197_ = v_isSharedCheck_7204_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_node_7194_);
                            lean_dec(v_v_7160_);
                            v___x_7196_ = lean_box(0);
                            v_isShared_7197_ = v_isSharedCheck_7204_;
                            state = 8;
                            continue;
                        }
                    }
                    _ => {
                        v___x_7205_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_7205_, 0, v_x_7147_);
                        lean_ctor_set(v___x_7205_, 1, v_x_7148_);
                        v___y_7164_ = v___x_7205_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7165_ = lean_array_fset(v_xs_x27_7162_, v_j_7154_, v___y_7164_);
                lean_dec(v_j_7154_);
                if v_isShared_7159_ == 0 {
                    lean_ctor_set(v___x_7158_, 0, v___x_7165_);
                    v___x_7167_ = v___x_7158_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7168_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7168_, 0, v___x_7165_);
                    v___x_7167_ = v_reuseFailAlloc_7168_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7167_;
            }
            4 => {
                v_fst_7177_ = lean_ctor_get(v_x_7147_, 0);
                v_snd_7178_ = lean_ctor_get(v_x_7147_, 1);
                v_fst_7179_ = lean_ctor_get(v_key_7169_, 0);
                v_snd_7180_ = lean_ctor_get(v_key_7169_, 1);
                v___x_7190_ = (lean_unbox(v_fst_7177_) as u8);
                if v___x_7190_ == 0 {
                    v___x_7191_ = (lean_unbox(v_fst_7179_) as u8);
                    if v___x_7191_ == 0 {
                        v___y_7182_ = v___x_7156_;
                        state = 6;
                        continue;
                    } else {
                        lean_del_object(v___x_7172_);
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_7192_ = (lean_unbox(v_fst_7179_) as u8);
                    v___y_7182_ = v___x_7192_;
                    state = 6;
                    continue;
                }
            }
            5 => {
                v___x_7175_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                    v_key_7169_,
                    v_val_7170_,
                    v_x_7147_,
                    v_x_7148_,
                );
                v___x_7176_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7176_, 0, v___x_7175_);
                v___y_7164_ = v___x_7176_;
                state = 2;
                continue;
            }
            6 => {
                if v___y_7182_ == 0 {
                    lean_del_object(v___x_7172_);
                    state = 5;
                    continue;
                } else {
                    v___x_7183_ = lean_array_get_size(v_snd_7178_);
                    v___x_7184_ = lean_array_get_size(v_snd_7180_);
                    v___x_7185_ = lean_nat_dec_eq(v___x_7183_, v___x_7184_);
                    if v___x_7185_ == 0 {
                        lean_del_object(v___x_7172_);
                        state = 5;
                        continue;
                    } else {
                        v___x_7186_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_7178_, v_snd_7180_, v___x_7183_);
                        if v___x_7186_ == 0 {
                            lean_del_object(v___x_7172_);
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_val_7170_);
                            lean_dec(v_key_7169_);
                            if v_isShared_7173_ == 0 {
                                lean_ctor_set(v___x_7172_, 1, v_x_7148_);
                                lean_ctor_set(v___x_7172_, 0, v_x_7147_);
                                v___x_7188_ = v___x_7172_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7189_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7189_, 0, v_x_7147_);
                                lean_ctor_set(v_reuseFailAlloc_7189_, 1, v_x_7148_);
                                v___x_7188_ = v_reuseFailAlloc_7189_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                v___y_7164_ = v___x_7188_;
                state = 2;
                continue;
            }
            8 => {
                v___x_7198_ = lean_usize_shift_right(v_x_7145_, v___x_7150_);
                v___x_7199_ = lean_usize_add(v_x_7146_, v___x_7151_);
                v___x_7200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_node_7194_, v___x_7198_, v___x_7199_, v_x_7147_, v_x_7148_);
                if v_isShared_7197_ == 0 {
                    lean_ctor_set(v___x_7196_, 0, v___x_7200_);
                    v___x_7202_ = v___x_7196_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7203_, 0, v___x_7200_);
                    v___x_7202_ = v_reuseFailAlloc_7203_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_7164_ = v___x_7202_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_7212_ == 0 {
                    v___x_7214_ = v___x_7211_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7228_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7228_, 0, v_ks_7208_);
                    lean_ctor_set(v_reuseFailAlloc_7228_, 1, v_vs_7209_);
                    v___x_7214_ = v_reuseFailAlloc_7228_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_newNode_7215_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v___x_7214_, v_x_7147_, v_x_7148_);
                v___x_7223_ = 7usize;
                v___x_7224_ = lean_usize_dec_le(v___x_7223_, v_x_7146_);
                if v___x_7224_ == 0 {
                    v___x_7225_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_7215_);
                    v___x_7226_ = lean_unsigned_to_nat(4);
                    v___x_7227_ = lean_nat_dec_lt(v___x_7225_, v___x_7226_);
                    lean_dec(v___x_7225_);
                    v___y_7217_ = v___x_7227_;
                    state = 12;
                    continue;
                } else {
                    v___y_7217_ = v___x_7224_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v___y_7217_ == 0 {
                    v_ks_7218_ = lean_ctor_get(v_newNode_7215_, 0);
                    lean_inc_ref(v_ks_7218_);
                    v_vs_7219_ = lean_ctor_get(v_newNode_7215_, 1);
                    lean_inc_ref(v_vs_7219_);
                    lean_dec_ref(v_newNode_7215_);
                    v___x_7220_ = lean_unsigned_to_nat(0);
                    v___x_7221_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0);
                    v___x_7222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_x_7146_, v_ks_7218_, v_vs_7219_, v___x_7220_, v___x_7221_);
                    lean_dec_ref(v_vs_7219_);
                    lean_dec_ref(v_ks_7218_);
                    return v___x_7222_;
                } else {
                    return v_newNode_7215_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_7230_: usize,
    mut v_keys_7231_: *mut LeanObject,
    mut v_vals_7232_: *mut LeanObject,
    mut v_i_7233_: *mut LeanObject,
    mut v_entries_7234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: u8 = 0;
    let mut v_k_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7242_: u64 = 0;
    let mut v___y_7243_: u64 = 0;
    let mut v___x_7244_: u64 = 0;
    let mut v_h_7245_: usize = 0;
    let mut v___x_7246_: usize = 0;
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: usize = 0;
    let mut v___x_7249_: usize = 0;
    let mut v___x_7250_: usize = 0;
    let mut v_h_7251_: usize = 0;
    let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7256_: u64 = 0;
    let mut v___x_7257_: u64 = 0;
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: u8 = 0;
    let mut v___x_7261_: u8 = 0;
    let mut v___x_7262_: usize = 0;
    let mut v___x_7263_: usize = 0;
    let mut v___x_7264_: u64 = 0;
    let mut v___x_7265_: usize = 0;
    let mut v___x_7266_: usize = 0;
    let mut v___x_7267_: u64 = 0;
    let mut v___x_7268_: u8 = 0;
    let mut v___x_7269_: u64 = 0;
    let mut v___x_7270_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7235_ = lean_array_get_size(v_keys_7231_);
                v___x_7236_ = lean_nat_dec_lt(v_i_7233_, v___x_7235_);
                if v___x_7236_ == 0 {
                    lean_dec(v_i_7233_);
                    return v_entries_7234_;
                } else {
                    v_k_7237_ = lean_array_fget_borrowed(v_keys_7231_, v_i_7233_);
                    v_fst_7238_ = lean_ctor_get(v_k_7237_, 0);
                    v_snd_7239_ = lean_ctor_get(v_k_7237_, 1);
                    v_v_7240_ = lean_array_fget_borrowed(v_vals_7232_, v_i_7233_);
                    v___x_7268_ = (lean_unbox(v_fst_7238_) as u8);
                    if v___x_7268_ == 0 {
                        v___x_7269_ = 13u64;
                        v___y_7256_ = v___x_7269_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7270_ = 11u64;
                        v___y_7256_ = v___x_7270_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7244_ = lean_uint64_mix_hash(v___y_7242_, v___y_7243_);
                v_h_7245_ = lean_uint64_to_usize(v___x_7244_);
                v___x_7246_ = 5usize;
                v___x_7247_ = lean_unsigned_to_nat(1);
                v___x_7248_ = 1usize;
                v___x_7249_ = lean_usize_sub(v_depth_7230_, v___x_7248_);
                v___x_7250_ = lean_usize_mul(v___x_7246_, v___x_7249_);
                v_h_7251_ = lean_usize_shift_right(v_h_7245_, v___x_7250_);
                v___x_7252_ = lean_nat_add(v_i_7233_, v___x_7247_);
                lean_dec(v_i_7233_);
                lean_inc(v_v_7240_);
                lean_inc(v_k_7237_);
                v___x_7253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_entries_7234_, v_h_7251_, v_depth_7230_, v_k_7237_, v_v_7240_);
                v_i_7233_ = v___x_7252_;
                v_entries_7234_ = v___x_7253_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7257_ = 7u64;
                v___x_7258_ = lean_unsigned_to_nat(0);
                v___x_7259_ = lean_array_get_size(v_snd_7239_);
                v___x_7260_ = lean_nat_dec_lt(v___x_7258_, v___x_7259_);
                if v___x_7260_ == 0 {
                    v___y_7242_ = v___y_7256_;
                    v___y_7243_ = v___x_7257_;
                    state = 1;
                    continue;
                } else {
                    v___x_7261_ = lean_nat_dec_le(v___x_7259_, v___x_7259_);
                    if v___x_7261_ == 0 {
                        if v___x_7260_ == 0 {
                            v___y_7242_ = v___y_7256_;
                            v___y_7243_ = v___x_7257_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7262_ = 0usize;
                            v___x_7263_ = lean_usize_of_nat(v___x_7259_);
                            v___x_7264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7239_, v___x_7262_, v___x_7263_, v___x_7257_);
                            v___y_7242_ = v___y_7256_;
                            v___y_7243_ = v___x_7264_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7265_ = 0usize;
                        v___x_7266_ = lean_usize_of_nat(v___x_7259_);
                        v___x_7267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7239_, v___x_7265_, v___x_7266_, v___x_7257_);
                        v___y_7242_ = v___y_7256_;
                        v___y_7243_ = v___x_7267_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_7271_: *mut LeanObject,
    mut v_keys_7272_: *mut LeanObject,
    mut v_vals_7273_: *mut LeanObject,
    mut v_i_7274_: *mut LeanObject,
    mut v_entries_7275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_7276_: usize = 0;
    let mut v_res_7277_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_7276_ = lean_unbox_usize(v_depth_7271_);
    lean_dec(v_depth_7271_);
    v_res_7277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_7276_, v_keys_7272_, v_vals_7273_, v_i_7274_, v_entries_7275_);
    lean_dec_ref(v_vals_7273_);
    lean_dec_ref(v_keys_7272_);
    return v_res_7277_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_7278_: *mut LeanObject,
    mut v_x_7279_: *mut LeanObject,
    mut v_x_7280_: *mut LeanObject,
    mut v_x_7281_: *mut LeanObject,
    mut v_x_7282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2154__boxed_7283_: usize = 0;
    let mut v_x_2155__boxed_7284_: usize = 0;
    let mut v_res_7285_: *mut LeanObject = core::ptr::null_mut();
    v_x_2154__boxed_7283_ = lean_unbox_usize(v_x_7279_);
    lean_dec(v_x_7279_);
    v_x_2155__boxed_7284_ = lean_unbox_usize(v_x_7280_);
    lean_dec(v_x_7280_);
    v_res_7285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_7278_, v_x_2154__boxed_7283_, v_x_2155__boxed_7284_, v_x_7281_, v_x_7282_);
    return v_res_7285_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(
    mut v_x_7286_: *mut LeanObject,
    mut v_x_7287_: *mut LeanObject,
    mut v_x_7288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7290_: u64 = 0;
    let mut v___y_7291_: u64 = 0;
    let mut v___x_7292_: u64 = 0;
    let mut v___x_7293_: usize = 0;
    let mut v___x_7294_: usize = 0;
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7299_: u64 = 0;
    let mut v___x_7300_: u64 = 0;
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: u8 = 0;
    let mut v___x_7304_: u8 = 0;
    let mut v___x_7305_: usize = 0;
    let mut v___x_7306_: usize = 0;
    let mut v___x_7307_: u64 = 0;
    let mut v___x_7308_: usize = 0;
    let mut v___x_7309_: usize = 0;
    let mut v___x_7310_: u64 = 0;
    let mut v___x_7311_: u8 = 0;
    let mut v___x_7312_: u64 = 0;
    let mut v___x_7313_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7296_ = lean_ctor_get(v_x_7287_, 0);
                v_snd_7297_ = lean_ctor_get(v_x_7287_, 1);
                v___x_7311_ = (lean_unbox(v_fst_7296_) as u8);
                if v___x_7311_ == 0 {
                    v___x_7312_ = 13u64;
                    v___y_7299_ = v___x_7312_;
                    state = 2;
                    continue;
                } else {
                    v___x_7313_ = 11u64;
                    v___y_7299_ = v___x_7313_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_7292_ = lean_uint64_mix_hash(v___y_7290_, v___y_7291_);
                v___x_7293_ = lean_uint64_to_usize(v___x_7292_);
                v___x_7294_ = 1usize;
                v___x_7295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_7286_, v___x_7293_, v___x_7294_, v_x_7287_, v_x_7288_);
                return v___x_7295_;
            }
            2 => {
                v___x_7300_ = 7u64;
                v___x_7301_ = lean_unsigned_to_nat(0);
                v___x_7302_ = lean_array_get_size(v_snd_7297_);
                v___x_7303_ = lean_nat_dec_lt(v___x_7301_, v___x_7302_);
                if v___x_7303_ == 0 {
                    v___y_7290_ = v___y_7299_;
                    v___y_7291_ = v___x_7300_;
                    state = 1;
                    continue;
                } else {
                    v___x_7304_ = lean_nat_dec_le(v___x_7302_, v___x_7302_);
                    if v___x_7304_ == 0 {
                        if v___x_7303_ == 0 {
                            v___y_7290_ = v___y_7299_;
                            v___y_7291_ = v___x_7300_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7305_ = 0usize;
                            v___x_7306_ = lean_usize_of_nat(v___x_7302_);
                            v___x_7307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7297_, v___x_7305_, v___x_7306_, v___x_7300_);
                            v___y_7290_ = v___y_7299_;
                            v___y_7291_ = v___x_7307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7308_ = 0usize;
                        v___x_7309_ = lean_usize_of_nat(v___x_7302_);
                        v___x_7310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_7297_, v___x_7308_, v___x_7309_, v___x_7300_);
                        v___y_7290_ = v___y_7299_;
                        v___y_7291_ = v___x_7310_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(
    mut v_x_7314_: *mut LeanObject,
    mut v_x_7315_: *mut LeanObject,
    mut v_x_7316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_7317_: u8 = 0;
    let mut v_map_u2081_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7322_: u8 = 0;
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7327_: u8 = 0;
    let mut v_map_u2081_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7332_: u8 = 0;
    let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_7317_ = lean_ctor_get_uint8(
                    v_x_7314_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_7317_ == 0 {
                    v_map_u2081_7318_ = lean_ctor_get(v_x_7314_, 0);
                    v_map_u2082_7319_ = lean_ctor_get(v_x_7314_, 1);
                    v_isSharedCheck_7327_ = (!lean_is_exclusive(v_x_7314_)) as u8;
                    if v_isSharedCheck_7327_ == 0 {
                        v___x_7321_ = v_x_7314_;
                        v_isShared_7322_ = v_isSharedCheck_7327_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_7319_);
                        lean_inc(v_map_u2081_7318_);
                        lean_dec(v_x_7314_);
                        v___x_7321_ = lean_box(0);
                        v_isShared_7322_ = v_isSharedCheck_7327_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_7328_ = lean_ctor_get(v_x_7314_, 0);
                    v_map_u2082_7329_ = lean_ctor_get(v_x_7314_, 1);
                    v_isSharedCheck_7337_ = (!lean_is_exclusive(v_x_7314_)) as u8;
                    if v_isSharedCheck_7337_ == 0 {
                        v___x_7331_ = v_x_7314_;
                        v_isShared_7332_ = v_isSharedCheck_7337_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_7329_);
                        lean_inc(v_map_u2081_7328_);
                        lean_dec(v_x_7314_);
                        v___x_7331_ = lean_box(0);
                        v_isShared_7332_ = v_isSharedCheck_7337_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7323_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2082_7319_, v_x_7315_, v_x_7316_);
                if v_isShared_7322_ == 0 {
                    lean_ctor_set(v___x_7321_, 1, v___x_7323_);
                    v___x_7325_ = v___x_7321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7326_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7326_, 0, v_map_u2081_7318_);
                    lean_ctor_set(v_reuseFailAlloc_7326_, 1, v___x_7323_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7326_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_7317_,
                    );
                    v___x_7325_ = v_reuseFailAlloc_7326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7325_;
            }
            3 => {
                v___x_7333_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2081_7328_, v_x_7315_, v_x_7316_);
                if v_isShared_7332_ == 0 {
                    lean_ctor_set(v___x_7331_, 0, v___x_7333_);
                    v___x_7335_ = v___x_7331_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7336_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7336_, 0, v___x_7333_);
                    lean_ctor_set(v_reuseFailAlloc_7336_, 1, v_map_u2082_7329_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7336_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_7317_,
                    );
                    v___x_7335_ = v_reuseFailAlloc_7336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addCustomEliminatorEntry(
    mut v_es_7338_: *mut LeanObject,
    mut v_e_7339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_induction_7340_: u8 = 0;
    let mut v_typeNames_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimName_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    v_induction_7340_ = lean_ctor_get_uint8(
        v_e_7339_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_typeNames_7341_ = lean_ctor_get(v_e_7339_, 0);
    lean_inc_ref(v_typeNames_7341_);
    v_elimName_7342_ = lean_ctor_get(v_e_7339_, 1);
    lean_inc(v_elimName_7342_);
    lean_dec_ref(v_e_7339_);
    v___x_7343_ = lean_box((v_induction_7340_) as usize);
    v___x_7344_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7344_, 0, v___x_7343_);
    lean_ctor_set(v___x_7344_, 1, v_typeNames_7341_);
    v___x_7345_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(
        v_es_7338_,
        v___x_7344_,
        v_elimName_7342_,
    );
    return v___x_7345_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(
    mut v_00_u03b2_7346_: *mut LeanObject,
    mut v_x_7347_: *mut LeanObject,
    mut v_x_7348_: *mut LeanObject,
    mut v_x_7349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    v___x_7350_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(
        v_x_7347_, v_x_7348_, v_x_7349_,
    );
    return v___x_7350_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(
    mut v_00_u03b2_7351_: *mut LeanObject,
    mut v_x_7352_: *mut LeanObject,
    mut v_x_7353_: *mut LeanObject,
    mut v_x_7354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    v___x_7355_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_x_7352_, v_x_7353_, v_x_7354_);
    return v___x_7355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(
    mut v_00_u03b2_7356_: *mut LeanObject,
    mut v_m_7357_: *mut LeanObject,
    mut v_a_7358_: *mut LeanObject,
    mut v_b_7359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    v___x_7360_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_m_7357_, v_a_7358_, v_b_7359_);
    return v___x_7360_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_7361_: *mut LeanObject,
    mut v_x_7362_: *mut LeanObject,
    mut v_x_7363_: usize,
    mut v_x_7364_: usize,
    mut v_x_7365_: *mut LeanObject,
    mut v_x_7366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    v___x_7367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_7362_, v_x_7363_, v_x_7364_, v_x_7365_, v_x_7366_);
    return v___x_7367_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_7368_: *mut LeanObject,
    mut v_x_7369_: *mut LeanObject,
    mut v_x_7370_: *mut LeanObject,
    mut v_x_7371_: *mut LeanObject,
    mut v_x_7372_: *mut LeanObject,
    mut v_x_7373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2486__boxed_7374_: usize = 0;
    let mut v_x_2487__boxed_7375_: usize = 0;
    let mut v_res_7376_: *mut LeanObject = core::ptr::null_mut();
    v_x_2486__boxed_7374_ = lean_unbox_usize(v_x_7370_);
    lean_dec(v_x_7370_);
    v_x_2487__boxed_7375_ = lean_unbox_usize(v_x_7371_);
    lean_dec(v_x_7371_);
    v_res_7376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_7368_, v_x_7369_, v_x_2486__boxed_7374_, v_x_2487__boxed_7375_, v_x_7372_, v_x_7373_);
    return v_res_7376_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(
    mut v_00_u03b2_7377_: *mut LeanObject,
    mut v_a_7378_: *mut LeanObject,
    mut v_x_7379_: *mut LeanObject,
) -> u8 {
    let mut v___x_7380_: u8 = 0;
    v___x_7380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_7378_, v_x_7379_);
    return v___x_7380_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_7381_: *mut LeanObject,
    mut v_a_7382_: *mut LeanObject,
    mut v_x_7383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7384_: u8 = 0;
    let mut v_r_7385_: *mut LeanObject = core::ptr::null_mut();
    v_res_7384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_7381_, v_a_7382_, v_x_7383_);
    lean_dec(v_x_7383_);
    lean_dec_ref(v_a_7382_);
    v_r_7385_ = lean_box((v_res_7384_) as usize);
    return v_r_7385_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(
    mut v_00_u03b2_7386_: *mut LeanObject,
    mut v_data_7387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    v___x_7388_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_data_7387_);
    return v___x_7388_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(
    mut v_00_u03b2_7389_: *mut LeanObject,
    mut v_a_7390_: *mut LeanObject,
    mut v_b_7391_: *mut LeanObject,
    mut v_x_7392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
    v___x_7393_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_7390_, v_b_7391_, v_x_7392_);
    return v___x_7393_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_xs_7394_: *mut LeanObject,
    mut v_ys_7395_: *mut LeanObject,
    mut v_hsz_7396_: *mut LeanObject,
    mut v_x_7397_: *mut LeanObject,
    mut v_x_7398_: *mut LeanObject,
) -> u8 {
    let mut v___x_7399_: u8 = 0;
    v___x_7399_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_7394_, v_ys_7395_, v_x_7397_);
    return v___x_7399_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_xs_7400_: *mut LeanObject,
    mut v_ys_7401_: *mut LeanObject,
    mut v_hsz_7402_: *mut LeanObject,
    mut v_x_7403_: *mut LeanObject,
    mut v_x_7404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7405_: u8 = 0;
    let mut v_r_7406_: *mut LeanObject = core::ptr::null_mut();
    v_res_7405_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_7400_, v_ys_7401_, v_hsz_7402_, v_x_7403_, v_x_7404_);
    lean_dec_ref(v_ys_7401_);
    lean_dec_ref(v_xs_7400_);
    v_r_7406_ = lean_box((v_res_7405_) as usize);
    return v_r_7406_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_7407_: *mut LeanObject,
    mut v_n_7408_: *mut LeanObject,
    mut v_k_7409_: *mut LeanObject,
    mut v_v_7410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7411_: *mut LeanObject = core::ptr::null_mut();
    v___x_7411_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_n_7408_, v_k_7409_, v_v_7410_);
    return v___x_7411_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_7412_: *mut LeanObject,
    mut v_depth_7413_: usize,
    mut v_keys_7414_: *mut LeanObject,
    mut v_vals_7415_: *mut LeanObject,
    mut v_heq_7416_: *mut LeanObject,
    mut v_i_7417_: *mut LeanObject,
    mut v_entries_7418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    v___x_7419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_7413_, v_keys_7414_, v_vals_7415_, v_i_7417_, v_entries_7418_);
    return v___x_7419_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_7420_: *mut LeanObject,
    mut v_depth_7421_: *mut LeanObject,
    mut v_keys_7422_: *mut LeanObject,
    mut v_vals_7423_: *mut LeanObject,
    mut v_heq_7424_: *mut LeanObject,
    mut v_i_7425_: *mut LeanObject,
    mut v_entries_7426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_7427_: usize = 0;
    let mut v_res_7428_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_7427_ = lean_unbox_usize(v_depth_7421_);
    lean_dec(v_depth_7421_);
    v_res_7428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_7420_, v_depth_boxed_7427_, v_keys_7422_, v_vals_7423_, v_heq_7424_, v_i_7425_, v_entries_7426_);
    lean_dec_ref(v_vals_7423_);
    lean_dec_ref(v_keys_7422_);
    return v_res_7428_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(
    mut v_00_u03b2_7429_: *mut LeanObject,
    mut v_i_7430_: *mut LeanObject,
    mut v_source_7431_: *mut LeanObject,
    mut v_target_7432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    v___x_7433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v_i_7430_, v_source_7431_, v_target_7432_);
    return v___x_7433_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b2_7434_: *mut LeanObject,
    mut v_x_7435_: *mut LeanObject,
    mut v_x_7436_: *mut LeanObject,
    mut v_x_7437_: *mut LeanObject,
    mut v_x_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    v___x_7439_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_x_7435_, v_x_7436_, v_x_7437_, v_x_7438_);
    return v___x_7439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(
    mut v_00_u03b2_7440_: *mut LeanObject,
    mut v_x_7441_: *mut LeanObject,
    mut v_x_7442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7443_: *mut LeanObject = core::ptr::null_mut();
    v___x_7443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_x_7441_, v_x_7442_);
    return v___x_7443_;
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_7444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_7445_: u8 = 0;
    let mut v_map_u2081_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7450_: u8 = 0;
    let mut v___x_7451_: u8 = 0;
    let mut v___x_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_7445_ = lean_ctor_get_uint8(
                    v_m_7444_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_7445_ == 0 {
                    return v_m_7444_;
                } else {
                    v_map_u2081_7446_ = lean_ctor_get(v_m_7444_, 0);
                    v_map_u2082_7447_ = lean_ctor_get(v_m_7444_, 1);
                    v_isSharedCheck_7455_ = (!lean_is_exclusive(v_m_7444_)) as u8;
                    if v_isSharedCheck_7455_ == 0 {
                        v___x_7449_ = v_m_7444_;
                        v_isShared_7450_ = v_isSharedCheck_7455_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_7447_);
                        lean_inc(v_map_u2081_7446_);
                        lean_dec(v_m_7444_);
                        v___x_7449_ = lean_box(0);
                        v_isShared_7450_ = v_isSharedCheck_7455_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7451_ = 0;
                if v_isShared_7450_ == 0 {
                    v___x_7453_ = v___x_7449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7454_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7454_, 0, v_map_u2081_7446_);
                    lean_ctor_set(v_reuseFailAlloc_7454_, 1, v_map_u2082_7447_);
                    v___x_7453_ = v_reuseFailAlloc_7454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_7453_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_7451_,
                );
                return v___x_7453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_7456_: *mut LeanObject,
    mut v_m_7457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7458_: *mut LeanObject = core::ptr::null_mut();
    v___x_7458_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_7457_);
    return v___x_7458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(
    mut v_x_7459_: *mut LeanObject,
    mut v_a_7460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    v___x_7461_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7461_, 0, v_a_7460_);
    lean_inc_ref_n(v___x_7461_, 2);
    v___x_7462_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7462_, 0, v___x_7461_);
    lean_ctor_set(v___x_7462_, 1, v___x_7461_);
    lean_ctor_set(v___x_7462_, 2, v___x_7461_);
    return v___x_7462_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(
    mut v_x_7463_: *mut LeanObject,
    mut v_a_7464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7465_: *mut LeanObject = core::ptr::null_mut();
    v_res_7465_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_7463_, v_a_7464_);
    lean_dec_ref(v_x_7463_);
    return v_res_7465_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    v___f_7476_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
    v___f_7477_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
    v___x_7478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once
        ),
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4,
    );
    v___x_7479_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
    v___x_7480_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
    v___x_7481_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_7481_, 0, v___x_7480_);
    lean_ctor_set(v___x_7481_, 1, v___x_7479_);
    lean_ctor_set(v___x_7481_, 2, v___x_7478_);
    lean_ctor_set(v___x_7481_, 3, v___f_7477_);
    lean_ctor_set(v___x_7481_, 4, v___f_7476_);
    return v___x_7481_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    v___x_7483_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
    v___x_7484_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_7483_);
    return v___x_7484_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(
    mut v_a_7485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7486_: *mut LeanObject = core::ptr::null_mut();
    v_res_7486_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
    return v_res_7486_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(
    mut v_x_7487_: *mut LeanObject,
) -> u8 {
    let mut v___x_7488_: u8 = 0;
    v___x_7488_ = 0;
    return v___x_7488_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(
    mut v_x_7489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7490_: u8 = 0;
    let mut v_r_7491_: *mut LeanObject = core::ptr::null_mut();
    v_res_7490_ =
        l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(
            v_x_7489_,
        );
    lean_dec(v_x_7489_);
    v_r_7491_ = lean_box((v_res_7490_) as usize);
    return v_r_7491_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(
    mut v_fvarId_7492_: *mut LeanObject,
    mut v_x_7493_: *mut LeanObject,
) -> u8 {
    let mut v___x_7494_: u8 = 0;
    v___x_7494_ = l_Lean_instBEqFVarId_beq(v_fvarId_7492_, v_x_7493_);
    return v___x_7494_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(
    mut v_fvarId_7495_: *mut LeanObject,
    mut v_x_7496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7497_: u8 = 0;
    let mut v_r_7498_: *mut LeanObject = core::ptr::null_mut();
    v_res_7497_ =
        l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(
            v_fvarId_7495_,
            v_x_7496_,
        );
    lean_dec(v_x_7496_);
    lean_dec(v_fvarId_7495_);
    v_r_7498_ = lean_box((v_res_7497_) as usize);
    return v_r_7498_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    v___x_7500_ = lean_box(0);
    v___x_7501_ = lean_unsigned_to_nat(16);
    v___x_7502_ = lean_mk_array(v___x_7501_, v___x_7500_);
    return v___x_7502_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    v___x_7503_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once), _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
    v___x_7504_ = lean_unsigned_to_nat(0);
    v___x_7505_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7505_, 0, v___x_7504_);
    lean_ctor_set(v___x_7505_, 1, v___x_7503_);
    return v___x_7505_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(
    mut v_e_7506_: *mut LeanObject,
    mut v_fvarId_7507_: *mut LeanObject,
    mut v___y_7508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7512_: u8 = 0;
    let mut v_mctx_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7521_: u8 = 0;
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7528_: u8 = 0;
    let mut v_unused_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: u8 = 0;
    let mut v_mctx_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: u8 = 0;
    let mut v___x_7542_: u8 = 0;
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7510_ = lean_st_ref_get(v___y_7508_);
                v_mctx_7536_ = lean_ctor_get(v___x_7510_, 0);
                lean_inc_ref_n(v_mctx_7536_, 2);
                lean_dec(v___x_7510_);
                v___f_7537_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0;
                v___f_7538_ = lean_alloc_closure(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_7538_, 0, v_fvarId_7507_);
                v___x_7539_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once), _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
                v___x_7540_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7540_, 0, v___x_7539_);
                lean_ctor_set(v___x_7540_, 1, v_mctx_7536_);
                v___x_7541_ = l_Lean_Expr_hasFVar(v_e_7506_);
                if v___x_7541_ == 0 {
                    v___x_7542_ = l_Lean_Expr_hasMVar(v_e_7506_);
                    if v___x_7542_ == 0 {
                        lean_dec_ref_known(v___x_7540_, 2);
                        lean_dec_ref(v___f_7538_);
                        lean_dec_ref(v_e_7506_);
                        v_fst_7512_ = v___x_7542_;
                        v_mctx_7513_ = v_mctx_7536_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_mctx_7536_);
                        v___x_7543_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_7538_,
                            v___f_7537_,
                            v_e_7506_,
                            v___x_7540_,
                        );
                        v___y_7531_ = v___x_7543_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mctx_7536_);
                    v___x_7544_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_7538_,
                        v___f_7537_,
                        v_e_7506_,
                        v___x_7540_,
                    );
                    v___y_7531_ = v___x_7544_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_7514_ = lean_st_ref_take(v___y_7508_);
                v_cache_7515_ = lean_ctor_get(v___x_7514_, 1);
                v_zetaDeltaFVarIds_7516_ = lean_ctor_get(v___x_7514_, 2);
                v_postponed_7517_ = lean_ctor_get(v___x_7514_, 3);
                v_diag_7518_ = lean_ctor_get(v___x_7514_, 4);
                v_isSharedCheck_7528_ = (!lean_is_exclusive(v___x_7514_)) as u8;
                if v_isSharedCheck_7528_ == 0 {
                    v_unused_7529_ = lean_ctor_get(v___x_7514_, 0);
                    lean_dec(v_unused_7529_);
                    v___x_7520_ = v___x_7514_;
                    v_isShared_7521_ = v_isSharedCheck_7528_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_diag_7518_);
                    lean_inc(v_postponed_7517_);
                    lean_inc(v_zetaDeltaFVarIds_7516_);
                    lean_inc(v_cache_7515_);
                    lean_dec(v___x_7514_);
                    v___x_7520_ = lean_box(0);
                    v_isShared_7521_ = v_isSharedCheck_7528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_7521_ == 0 {
                    lean_ctor_set(v___x_7520_, 0, v_mctx_7513_);
                    v___x_7523_ = v___x_7520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7527_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 0, v_mctx_7513_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 1, v_cache_7515_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 2, v_zetaDeltaFVarIds_7516_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 3, v_postponed_7517_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 4, v_diag_7518_);
                    v___x_7523_ = v_reuseFailAlloc_7527_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7524_ = lean_st_ref_set(v___y_7508_, v___x_7523_);
                v___x_7525_ = lean_box((v_fst_7512_) as usize);
                v___x_7526_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7526_, 0, v___x_7525_);
                return v___x_7526_;
            }
            4 => {
                v_snd_7532_ = lean_ctor_get(v___y_7531_, 1);
                lean_inc(v_snd_7532_);
                v_fst_7533_ = lean_ctor_get(v___y_7531_, 0);
                lean_inc(v_fst_7533_);
                lean_dec_ref(v___y_7531_);
                v_mctx_7534_ = lean_ctor_get(v_snd_7532_, 1);
                lean_inc_ref(v_mctx_7534_);
                lean_dec(v_snd_7532_);
                v___x_7535_ = (lean_unbox(v_fst_7533_) as u8);
                lean_dec(v_fst_7533_);
                v_fst_7512_ = v___x_7535_;
                v_mctx_7513_ = v_mctx_7534_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(
    mut v_e_7545_: *mut LeanObject,
    mut v_fvarId_7546_: *mut LeanObject,
    mut v___y_7547_: *mut LeanObject,
    mut v___y_7548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7549_: *mut LeanObject = core::ptr::null_mut();
    v_res_7549_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(
        v_e_7545_,
        v_fvarId_7546_,
        v___y_7547_,
    );
    lean_dec(v___y_7547_);
    return v_res_7549_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(
    mut v_e_7550_: *mut LeanObject,
    mut v_fvarId_7551_: *mut LeanObject,
    mut v___y_7552_: *mut LeanObject,
    mut v___y_7553_: *mut LeanObject,
    mut v___y_7554_: *mut LeanObject,
    mut v___y_7555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7557_: *mut LeanObject = core::ptr::null_mut();
    v___x_7557_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(
        v_e_7550_,
        v_fvarId_7551_,
        v___y_7553_,
    );
    return v___x_7557_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(
    mut v_e_7558_: *mut LeanObject,
    mut v_fvarId_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___y_7561_: *mut LeanObject,
    mut v___y_7562_: *mut LeanObject,
    mut v___y_7563_: *mut LeanObject,
    mut v___y_7564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7565_: *mut LeanObject = core::ptr::null_mut();
    v_res_7565_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(
        v_e_7558_,
        v_fvarId_7559_,
        v___y_7560_,
        v___y_7561_,
        v___y_7562_,
        v___y_7563_,
    );
    lean_dec(v___y_7563_);
    lean_dec_ref(v___y_7562_);
    lean_dec(v___y_7561_);
    lean_dec_ref(v___y_7560_);
    return v_res_7565_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(
    mut v_upperBound_7569_: *mut LeanObject,
    mut v___x_7570_: *mut LeanObject,
    mut v_xs_7571_: *mut LeanObject,
    mut v___x_7572_: *mut LeanObject,
    mut v_a_7573_: *mut LeanObject,
    mut v_b_7574_: *mut LeanObject,
    mut v___y_7575_: *mut LeanObject,
    mut v___y_7576_: *mut LeanObject,
    mut v___y_7577_: *mut LeanObject,
    mut v___y_7578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7592_: u8 = 0;
    let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: u8 = 0;
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7604_: u8 = 0;
    let mut v_a_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7608_: u8 = 0;
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7612_: u8 = 0;
    let mut v_a_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7616_: u8 = 0;
    let mut v___x_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7580_ = lean_nat_dec_lt(v_a_7573_, v_upperBound_7569_);
                if v___x_7580_ == 0 {
                    lean_dec(v_a_7573_);
                    v___x_7581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7581_, 0, v_b_7574_);
                    return v___x_7581_;
                } else {
                    lean_dec_ref(v_b_7574_);
                    v___x_7582_ = l_Lean_instInhabitedExpr;
                    v___x_7583_ = lean_array_fget_borrowed(v___x_7570_, v_a_7573_);
                    v___x_7584_ = lean_array_get_borrowed(v___x_7582_, v_xs_7571_, v___x_7583_);
                    lean_inc(v___y_7578_);
                    lean_inc_ref(v___y_7577_);
                    lean_inc(v___y_7576_);
                    lean_inc_ref(v___y_7575_);
                    lean_inc(v___x_7584_);
                    v___x_7585_ = lean_infer_type(
                        v___x_7584_,
                        v___y_7575_,
                        v___y_7576_,
                        v___y_7577_,
                        v___y_7578_,
                    );
                    if lean_obj_tag(v___x_7585_) == 0 {
                        v_a_7586_ = lean_ctor_get(v___x_7585_, 0);
                        lean_inc(v_a_7586_);
                        lean_dec_ref_known(v___x_7585_, 1);
                        v___x_7587_ = l_Lean_Expr_fvarId_x21(v___x_7572_);
                        v___x_7588_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_7586_, v___x_7587_, v___y_7576_);
                        if lean_obj_tag(v___x_7588_) == 0 {
                            v_a_7589_ = lean_ctor_get(v___x_7588_, 0);
                            v_isSharedCheck_7604_ = (!lean_is_exclusive(v___x_7588_)) as u8;
                            if v_isSharedCheck_7604_ == 0 {
                                v___x_7591_ = v___x_7588_;
                                v_isShared_7592_ = v_isSharedCheck_7604_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_7589_);
                                lean_dec(v___x_7588_);
                                v___x_7591_ = lean_box(0);
                                v_isShared_7592_ = v_isSharedCheck_7604_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_7573_);
                            v_a_7605_ = lean_ctor_get(v___x_7588_, 0);
                            v_isSharedCheck_7612_ = (!lean_is_exclusive(v___x_7588_)) as u8;
                            if v_isSharedCheck_7612_ == 0 {
                                v___x_7607_ = v___x_7588_;
                                v_isShared_7608_ = v_isSharedCheck_7612_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_7605_);
                                lean_dec(v___x_7588_);
                                v___x_7607_ = lean_box(0);
                                v_isShared_7608_ = v_isSharedCheck_7612_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_7573_);
                        v_a_7613_ = lean_ctor_get(v___x_7585_, 0);
                        v_isSharedCheck_7620_ = (!lean_is_exclusive(v___x_7585_)) as u8;
                        if v_isSharedCheck_7620_ == 0 {
                            v___x_7615_ = v___x_7585_;
                            v_isShared_7616_ = v_isSharedCheck_7620_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_7613_);
                            lean_dec(v___x_7585_);
                            v___x_7615_ = lean_box(0);
                            v_isShared_7616_ = v_isSharedCheck_7620_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7593_ = lean_box(0);
                v___x_7594_ = (lean_unbox(v_a_7589_) as u8);
                if v___x_7594_ == 0 {
                    lean_del_object(v___x_7591_);
                    lean_dec(v_a_7589_);
                    v___x_7595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0;
                    v___x_7596_ = lean_unsigned_to_nat(1);
                    v___x_7597_ = lean_nat_add(v_a_7573_, v___x_7596_);
                    lean_dec(v_a_7573_);
                    v_a_7573_ = v___x_7597_;
                    v_b_7574_ = v___x_7595_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_7573_);
                    v___x_7599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7599_, 0, v_a_7589_);
                    v___x_7600_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7600_, 0, v___x_7599_);
                    lean_ctor_set(v___x_7600_, 1, v___x_7593_);
                    if v_isShared_7592_ == 0 {
                        lean_ctor_set(v___x_7591_, 0, v___x_7600_);
                        v___x_7602_ = v___x_7591_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7603_, 0, v___x_7600_);
                        v___x_7602_ = v_reuseFailAlloc_7603_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7602_;
            }
            3 => {
                if v_isShared_7608_ == 0 {
                    v___x_7610_ = v___x_7607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7611_, 0, v_a_7605_);
                    v___x_7610_ = v_reuseFailAlloc_7611_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7610_;
            }
            5 => {
                if v_isShared_7616_ == 0 {
                    v___x_7618_ = v___x_7615_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7619_, 0, v_a_7613_);
                    v___x_7618_ = v_reuseFailAlloc_7619_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(
    mut v_upperBound_7621_: *mut LeanObject,
    mut v___x_7622_: *mut LeanObject,
    mut v_xs_7623_: *mut LeanObject,
    mut v___x_7624_: *mut LeanObject,
    mut v_a_7625_: *mut LeanObject,
    mut v_b_7626_: *mut LeanObject,
    mut v___y_7627_: *mut LeanObject,
    mut v___y_7628_: *mut LeanObject,
    mut v___y_7629_: *mut LeanObject,
    mut v___y_7630_: *mut LeanObject,
    mut v___y_7631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7632_: *mut LeanObject = core::ptr::null_mut();
    v_res_7632_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(
            v_upperBound_7621_,
            v___x_7622_,
            v_xs_7623_,
            v___x_7624_,
            v_a_7625_,
            v_b_7626_,
            v___y_7627_,
            v___y_7628_,
            v___y_7629_,
            v___y_7630_,
        );
    lean_dec(v___y_7630_);
    lean_dec_ref(v___y_7629_);
    lean_dec(v___y_7628_);
    lean_dec_ref(v___y_7627_);
    lean_dec_ref(v___x_7624_);
    lean_dec_ref(v_xs_7623_);
    lean_dec_ref(v___x_7622_);
    lean_dec(v_upperBound_7621_);
    return v_res_7632_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
    v___x_7634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0;
    v___x_7635_ = l_Lean_stringToMessageData(v___x_7634_);
    return v___x_7635_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(
    mut v_upperBound_7636_: *mut LeanObject,
    mut v___x_7637_: *mut LeanObject,
    mut v___x_7638_: *mut LeanObject,
    mut v_xs_7639_: *mut LeanObject,
    mut v_a_7640_: *mut LeanObject,
    mut v_b_7641_: *mut LeanObject,
    mut v___y_7642_: *mut LeanObject,
    mut v___y_7643_: *mut LeanObject,
    mut v___y_7644_: *mut LeanObject,
    mut v___y_7645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: u8 = 0;
    let mut v___x_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7672_: u8 = 0;
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_a_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7680_: u8 = 0;
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7684_: u8 = 0;
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: u8 = 0;
    let mut v_a_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7694_: u8 = 0;
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7652_ = lean_nat_dec_lt(v_a_7640_, v_upperBound_7636_);
                if v___x_7652_ == 0 {
                    lean_dec(v_a_7640_);
                    v___x_7653_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7653_, 0, v_b_7641_);
                    return v___x_7653_;
                } else {
                    v___x_7654_ = l_Lean_instInhabitedExpr;
                    v___x_7655_ = lean_unsigned_to_nat(1);
                    v___x_7656_ = lean_nat_add(v_a_7640_, v___x_7655_);
                    v___x_7657_ = lean_array_fget_borrowed(v___x_7638_, v_a_7640_);
                    v___x_7658_ = lean_array_get_borrowed(v___x_7654_, v_xs_7639_, v___x_7657_);
                    v___x_7685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0;
                    v___x_7686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_7637_, v___x_7638_, v_xs_7639_, v___x_7658_, v___x_7656_, v___x_7685_, v___y_7642_, v___y_7643_, v___y_7644_, v___y_7645_);
                    if lean_obj_tag(v___x_7686_) == 0 {
                        v_a_7687_ = lean_ctor_get(v___x_7686_, 0);
                        lean_inc(v_a_7687_);
                        lean_dec_ref_known(v___x_7686_, 1);
                        v_fst_7688_ = lean_ctor_get(v_a_7687_, 0);
                        lean_inc(v_fst_7688_);
                        lean_dec(v_a_7687_);
                        if lean_obj_tag(v_fst_7688_) == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_val_7689_ = lean_ctor_get(v_fst_7688_, 0);
                            lean_inc(v_val_7689_);
                            lean_dec_ref_known(v_fst_7688_, 1);
                            v___x_7690_ = (lean_unbox(v_val_7689_) as u8);
                            lean_dec(v_val_7689_);
                            if v___x_7690_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v_a_7648_ = v_b_7641_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_7641_);
                        lean_dec(v_a_7640_);
                        v_a_7691_ = lean_ctor_get(v___x_7686_, 0);
                        v_isSharedCheck_7698_ = (!lean_is_exclusive(v___x_7686_)) as u8;
                        if v_isSharedCheck_7698_ == 0 {
                            v___x_7693_ = v___x_7686_;
                            v_isShared_7694_ = v_isSharedCheck_7698_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_7691_);
                            lean_dec(v___x_7686_);
                            v___x_7693_ = lean_box(0);
                            v_isShared_7694_ = v_isSharedCheck_7698_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7649_ = lean_unsigned_to_nat(1);
                v___x_7650_ = lean_nat_add(v_a_7640_, v___x_7649_);
                lean_dec(v_a_7640_);
                v_a_7640_ = v___x_7650_;
                v_b_7641_ = v_a_7648_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___y_7645_);
                lean_inc_ref(v___y_7644_);
                lean_inc(v___y_7643_);
                lean_inc_ref(v___y_7642_);
                lean_inc(v___x_7658_);
                v___x_7660_ = lean_infer_type(
                    v___x_7658_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                    v___y_7645_,
                );
                if lean_obj_tag(v___x_7660_) == 0 {
                    v_a_7661_ = lean_ctor_get(v___x_7660_, 0);
                    lean_inc(v_a_7661_);
                    lean_dec_ref_known(v___x_7660_, 1);
                    v___x_7662_ = l_Lean_Expr_getAppFn(v_a_7661_);
                    if lean_obj_tag(v___x_7662_) == 4 {
                        lean_dec(v_a_7661_);
                        v_declName_7663_ = lean_ctor_get(v___x_7662_, 0);
                        lean_inc(v_declName_7663_);
                        lean_dec_ref_known(v___x_7662_, 2);
                        v___x_7664_ = lean_array_push(v_b_7641_, v_declName_7663_);
                        v_a_7648_ = v___x_7664_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_7662_);
                        v___x_7665_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
                        v___x_7666_ = l_Lean_indentExpr(v_a_7661_);
                        v___x_7667_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7667_, 0, v___x_7665_);
                        lean_ctor_set(v___x_7667_, 1, v___x_7666_);
                        v___x_7668_ =
                            l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
                                v___x_7667_,
                                v___y_7642_,
                                v___y_7643_,
                                v___y_7644_,
                                v___y_7645_,
                            );
                        if lean_obj_tag(v___x_7668_) == 0 {
                            lean_dec_ref_known(v___x_7668_, 1);
                            v_a_7648_ = v_b_7641_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_7641_);
                            lean_dec(v_a_7640_);
                            v_a_7669_ = lean_ctor_get(v___x_7668_, 0);
                            v_isSharedCheck_7676_ = (!lean_is_exclusive(v___x_7668_)) as u8;
                            if v_isSharedCheck_7676_ == 0 {
                                v___x_7671_ = v___x_7668_;
                                v_isShared_7672_ = v_isSharedCheck_7676_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_7669_);
                                lean_dec(v___x_7668_);
                                v___x_7671_ = lean_box(0);
                                v_isShared_7672_ = v_isSharedCheck_7676_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_b_7641_);
                    lean_dec(v_a_7640_);
                    v_a_7677_ = lean_ctor_get(v___x_7660_, 0);
                    v_isSharedCheck_7684_ = (!lean_is_exclusive(v___x_7660_)) as u8;
                    if v_isSharedCheck_7684_ == 0 {
                        v___x_7679_ = v___x_7660_;
                        v_isShared_7680_ = v_isSharedCheck_7684_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7677_);
                        lean_dec(v___x_7660_);
                        v___x_7679_ = lean_box(0);
                        v_isShared_7680_ = v_isSharedCheck_7684_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7672_ == 0 {
                    v___x_7674_ = v___x_7671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7675_, 0, v_a_7669_);
                    v___x_7674_ = v_reuseFailAlloc_7675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7674_;
            }
            5 => {
                if v_isShared_7680_ == 0 {
                    v___x_7682_ = v___x_7679_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7683_, 0, v_a_7677_);
                    v___x_7682_ = v_reuseFailAlloc_7683_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7682_;
            }
            7 => {
                if v_isShared_7694_ == 0 {
                    v___x_7696_ = v___x_7693_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7697_, 0, v_a_7691_);
                    v___x_7696_ = v_reuseFailAlloc_7697_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(
    mut v_upperBound_7699_: *mut LeanObject,
    mut v___x_7700_: *mut LeanObject,
    mut v___x_7701_: *mut LeanObject,
    mut v_xs_7702_: *mut LeanObject,
    mut v_a_7703_: *mut LeanObject,
    mut v_b_7704_: *mut LeanObject,
    mut v___y_7705_: *mut LeanObject,
    mut v___y_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
    mut v___y_7708_: *mut LeanObject,
    mut v___y_7709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7710_: *mut LeanObject = core::ptr::null_mut();
    v_res_7710_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(
            v_upperBound_7699_,
            v___x_7700_,
            v___x_7701_,
            v_xs_7702_,
            v_a_7703_,
            v_b_7704_,
            v___y_7705_,
            v___y_7706_,
            v___y_7707_,
            v___y_7708_,
        );
    lean_dec(v___y_7708_);
    lean_dec_ref(v___y_7707_);
    lean_dec(v___y_7706_);
    lean_dec_ref(v___y_7705_);
    lean_dec_ref(v_xs_7702_);
    lean_dec_ref(v___x_7701_);
    lean_dec(v___x_7700_);
    lean_dec(v_upperBound_7699_);
    return v_res_7710_;
}
pub unsafe fn l_Lean_Meta_mkCustomEliminator___lam__0(
    mut v_a_7711_: *mut LeanObject,
    mut v_induction_7712_: u8,
    mut v_elimName_7713_: *mut LeanObject,
    mut v_xs_7714_: *mut LeanObject,
    mut v_x_7715_: *mut LeanObject,
    mut v___y_7716_: *mut LeanObject,
    mut v___y_7717_: *mut LeanObject,
    mut v___y_7718_: *mut LeanObject,
    mut v___y_7719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_targetsPos_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7729_: u8 = 0;
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v_a_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7738_: u8 = 0;
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetsPos_7721_ = lean_ctor_get(v_a_7711_, 3);
                v___x_7722_ = lean_array_get_size(v_targetsPos_7721_);
                v___x_7723_ = lean_unsigned_to_nat(0);
                v___x_7724_ = l_Lean_Meta_addImplicitTargets___closed__0;
                v___x_7725_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_7722_, v___x_7722_, v_targetsPos_7721_, v_xs_7714_, v___x_7723_, v___x_7724_, v___y_7716_, v___y_7717_, v___y_7718_, v___y_7719_);
                if lean_obj_tag(v___x_7725_) == 0 {
                    v_a_7726_ = lean_ctor_get(v___x_7725_, 0);
                    v_isSharedCheck_7734_ = (!lean_is_exclusive(v___x_7725_)) as u8;
                    if v_isSharedCheck_7734_ == 0 {
                        v___x_7728_ = v___x_7725_;
                        v_isShared_7729_ = v_isSharedCheck_7734_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7726_);
                        lean_dec(v___x_7725_);
                        v___x_7728_ = lean_box(0);
                        v_isShared_7729_ = v_isSharedCheck_7734_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_elimName_7713_);
                    v_a_7735_ = lean_ctor_get(v___x_7725_, 0);
                    v_isSharedCheck_7742_ = (!lean_is_exclusive(v___x_7725_)) as u8;
                    if v_isSharedCheck_7742_ == 0 {
                        v___x_7737_ = v___x_7725_;
                        v_isShared_7738_ = v_isSharedCheck_7742_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7735_);
                        lean_dec(v___x_7725_);
                        v___x_7737_ = lean_box(0);
                        v_isShared_7738_ = v_isSharedCheck_7742_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7730_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_7730_, 0, v_a_7726_);
                lean_ctor_set(v___x_7730_, 1, v_elimName_7713_);
                lean_ctor_set_uint8(
                    v___x_7730_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_induction_7712_,
                );
                if v_isShared_7729_ == 0 {
                    lean_ctor_set(v___x_7728_, 0, v___x_7730_);
                    v___x_7732_ = v___x_7728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7733_, 0, v___x_7730_);
                    v___x_7732_ = v_reuseFailAlloc_7733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7732_;
            }
            3 => {
                if v_isShared_7738_ == 0 {
                    v___x_7740_ = v___x_7737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7741_, 0, v_a_7735_);
                    v___x_7740_ = v_reuseFailAlloc_7741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCustomEliminator___lam__0___boxed(
    mut v_a_7743_: *mut LeanObject,
    mut v_induction_7744_: *mut LeanObject,
    mut v_elimName_7745_: *mut LeanObject,
    mut v_xs_7746_: *mut LeanObject,
    mut v_x_7747_: *mut LeanObject,
    mut v___y_7748_: *mut LeanObject,
    mut v___y_7749_: *mut LeanObject,
    mut v___y_7750_: *mut LeanObject,
    mut v___y_7751_: *mut LeanObject,
    mut v___y_7752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_induction_boxed_7753_: u8 = 0;
    let mut v_res_7754_: *mut LeanObject = core::ptr::null_mut();
    v_induction_boxed_7753_ = (lean_unbox(v_induction_7744_) as u8);
    v_res_7754_ = l_Lean_Meta_mkCustomEliminator___lam__0(
        v_a_7743_,
        v_induction_boxed_7753_,
        v_elimName_7745_,
        v_xs_7746_,
        v_x_7747_,
        v___y_7748_,
        v___y_7749_,
        v___y_7750_,
        v___y_7751_,
    );
    lean_dec(v___y_7751_);
    lean_dec_ref(v___y_7750_);
    lean_dec(v___y_7749_);
    lean_dec_ref(v___y_7748_);
    lean_dec_ref(v_x_7747_);
    lean_dec_ref(v_xs_7746_);
    lean_dec_ref(v_a_7743_);
    return v_res_7754_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(
    mut v_ref_7755_: *mut LeanObject,
    mut v_msg_7756_: *mut LeanObject,
    mut v___y_7757_: *mut LeanObject,
    mut v___y_7758_: *mut LeanObject,
    mut v___y_7759_: *mut LeanObject,
    mut v___y_7760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7774_: u8 = 0;
    let mut v_cancelTk_x3f_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7776_: u8 = 0;
    let mut v_inheritedTraceOptions_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7780_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_7762_ = lean_ctor_get(v___y_7759_, 0);
    v_fileMap_7763_ = lean_ctor_get(v___y_7759_, 1);
    v_options_7764_ = lean_ctor_get(v___y_7759_, 2);
    v_currRecDepth_7765_ = lean_ctor_get(v___y_7759_, 3);
    v_maxRecDepth_7766_ = lean_ctor_get(v___y_7759_, 4);
    v_ref_7767_ = lean_ctor_get(v___y_7759_, 5);
    v_currNamespace_7768_ = lean_ctor_get(v___y_7759_, 6);
    v_openDecls_7769_ = lean_ctor_get(v___y_7759_, 7);
    v_initHeartbeats_7770_ = lean_ctor_get(v___y_7759_, 8);
    v_maxHeartbeats_7771_ = lean_ctor_get(v___y_7759_, 9);
    v_quotContext_7772_ = lean_ctor_get(v___y_7759_, 10);
    v_currMacroScope_7773_ = lean_ctor_get(v___y_7759_, 11);
    v_diag_7774_ = lean_ctor_get_uint8(
        v___y_7759_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_7775_ = lean_ctor_get(v___y_7759_, 12);
    v_suppressElabErrors_7776_ = lean_ctor_get_uint8(
        v___y_7759_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_7777_ = lean_ctor_get(v___y_7759_, 13);
    v_ref_7778_ = l_Lean_replaceRef(v_ref_7755_, v_ref_7767_);
    lean_inc_ref(v_inheritedTraceOptions_7777_);
    lean_inc(v_cancelTk_x3f_7775_);
    lean_inc(v_currMacroScope_7773_);
    lean_inc(v_quotContext_7772_);
    lean_inc(v_maxHeartbeats_7771_);
    lean_inc(v_initHeartbeats_7770_);
    lean_inc(v_openDecls_7769_);
    lean_inc(v_currNamespace_7768_);
    lean_inc(v_maxRecDepth_7766_);
    lean_inc(v_currRecDepth_7765_);
    lean_inc_ref(v_options_7764_);
    lean_inc_ref(v_fileMap_7763_);
    lean_inc_ref(v_fileName_7762_);
    v___x_7779_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_7779_, 0, v_fileName_7762_);
    lean_ctor_set(v___x_7779_, 1, v_fileMap_7763_);
    lean_ctor_set(v___x_7779_, 2, v_options_7764_);
    lean_ctor_set(v___x_7779_, 3, v_currRecDepth_7765_);
    lean_ctor_set(v___x_7779_, 4, v_maxRecDepth_7766_);
    lean_ctor_set(v___x_7779_, 5, v_ref_7778_);
    lean_ctor_set(v___x_7779_, 6, v_currNamespace_7768_);
    lean_ctor_set(v___x_7779_, 7, v_openDecls_7769_);
    lean_ctor_set(v___x_7779_, 8, v_initHeartbeats_7770_);
    lean_ctor_set(v___x_7779_, 9, v_maxHeartbeats_7771_);
    lean_ctor_set(v___x_7779_, 10, v_quotContext_7772_);
    lean_ctor_set(v___x_7779_, 11, v_currMacroScope_7773_);
    lean_ctor_set(v___x_7779_, 12, v_cancelTk_x3f_7775_);
    lean_ctor_set(v___x_7779_, 13, v_inheritedTraceOptions_7777_);
    lean_ctor_set_uint8(
        v___x_7779_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_7774_,
    );
    lean_ctor_set_uint8(
        v___x_7779_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_7776_,
    );
    v___x_7780_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(
        v_msg_7756_,
        v___y_7757_,
        v___y_7758_,
        v___x_7779_,
        v___y_7760_,
    );
    lean_dec_ref_known(v___x_7779_, 14);
    return v___x_7780_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(
    mut v_ref_7781_: *mut LeanObject,
    mut v_msg_7782_: *mut LeanObject,
    mut v___y_7783_: *mut LeanObject,
    mut v___y_7784_: *mut LeanObject,
    mut v___y_7785_: *mut LeanObject,
    mut v___y_7786_: *mut LeanObject,
    mut v___y_7787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7788_: *mut LeanObject = core::ptr::null_mut();
    v_res_7788_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_7781_, v_msg_7782_, v___y_7783_, v___y_7784_, v___y_7785_, v___y_7786_);
    lean_dec(v___y_7786_);
    lean_dec_ref(v___y_7785_);
    lean_dec(v___y_7784_);
    lean_dec_ref(v___y_7783_);
    lean_dec(v_ref_7781_);
    return v_res_7788_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    v___x_7789_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_7789_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7791_: *mut LeanObject = core::ptr::null_mut();
    v___x_7790_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
    v___x_7791_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7791_, 0, v___x_7790_);
    return v___x_7791_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut LeanObject = core::ptr::null_mut();
    v___x_7792_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_7793_ = lean_unsigned_to_nat(0);
    v___x_7794_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_7794_, 0, v___x_7793_);
    lean_ctor_set(v___x_7794_, 1, v___x_7793_);
    lean_ctor_set(v___x_7794_, 2, v___x_7793_);
    lean_ctor_set(v___x_7794_, 3, v___x_7793_);
    lean_ctor_set(v___x_7794_, 4, v___x_7792_);
    lean_ctor_set(v___x_7794_, 5, v___x_7792_);
    lean_ctor_set(v___x_7794_, 6, v___x_7792_);
    lean_ctor_set(v___x_7794_, 7, v___x_7792_);
    lean_ctor_set(v___x_7794_, 8, v___x_7792_);
    lean_ctor_set(v___x_7794_, 9, v___x_7792_);
    return v___x_7794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    v___x_7795_ = lean_unsigned_to_nat(32);
    v___x_7796_ = lean_mk_empty_array_with_capacity(v___x_7795_);
    v___x_7797_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7797_, 0, v___x_7796_);
    return v___x_7797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_7798_: usize = 0;
    let mut v___x_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    v___x_7798_ = 5usize;
    v___x_7799_ = lean_unsigned_to_nat(0);
    v___x_7800_ = lean_unsigned_to_nat(32);
    v___x_7801_ = lean_mk_empty_array_with_capacity(v___x_7800_);
    v___x_7802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
    v___x_7803_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_7803_, 0, v___x_7802_);
    lean_ctor_set(v___x_7803_, 1, v___x_7801_);
    lean_ctor_set(v___x_7803_, 2, v___x_7799_);
    lean_ctor_set(v___x_7803_, 3, v___x_7799_);
    lean_ctor_set_usize(v___x_7803_, 4, v___x_7798_);
    return v___x_7803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    v___x_7804_ = lean_box(1);
    v___x_7805_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
    v___x_7806_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_7807_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7807_, 0, v___x_7806_);
    lean_ctor_set(v___x_7807_, 1, v___x_7805_);
    lean_ctor_set(v___x_7807_, 2, v___x_7804_);
    return v___x_7807_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut LeanObject = core::ptr::null_mut();
    v___x_7809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_7810_ = l_Lean_stringToMessageData(v___x_7809_);
    return v___x_7810_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    v___x_7812_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_7813_ = l_Lean_stringToMessageData(v___x_7812_);
    return v___x_7813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: *mut LeanObject = core::ptr::null_mut();
    v___x_7815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_7816_ = l_Lean_stringToMessageData(v___x_7815_);
    return v___x_7816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    v___x_7818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_7819_ = l_Lean_stringToMessageData(v___x_7818_);
    return v___x_7819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    v___x_7821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14;
    v___x_7822_ = l_Lean_stringToMessageData(v___x_7821_);
    return v___x_7822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    v___x_7824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16;
    v___x_7825_ = l_Lean_stringToMessageData(v___x_7824_);
    return v___x_7825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    v___x_7827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18;
    v___x_7828_ = l_Lean_stringToMessageData(v___x_7827_);
    return v___x_7828_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(
    mut v_msg_7829_: *mut LeanObject,
    mut v_declHint_7830_: *mut LeanObject,
    mut v___y_7831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: u8 = 0;
    let mut v_isExporting_7836_: u8 = 0;
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: u8 = 0;
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7858_: u8 = 0;
    let mut v___x_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: u8 = 0;
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7890_: u8 = 0;
    let mut v___x_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7833_ = lean_st_ref_get(v___y_7831_);
                v_env_7834_ = lean_ctor_get(v___x_7833_, 0);
                lean_inc_ref(v_env_7834_);
                lean_dec(v___x_7833_);
                v___x_7835_ = l_Lean_Name_isAnonymous(v_declHint_7830_);
                if v___x_7835_ == 0 {
                    v_isExporting_7836_ = lean_ctor_get_uint8(
                        v_env_7834_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_7836_ == 0 {
                        lean_dec_ref(v_env_7834_);
                        lean_dec(v_declHint_7830_);
                        v___x_7837_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7837_, 0, v_msg_7829_);
                        return v___x_7837_;
                    } else {
                        lean_inc_ref(v_env_7834_);
                        v___x_7838_ = l_Lean_Environment_setExporting(v_env_7834_, v___x_7835_);
                        lean_inc(v_declHint_7830_);
                        lean_inc_ref(v___x_7838_);
                        v___x_7839_ = l_Lean_Environment_contains(
                            v___x_7838_,
                            v_declHint_7830_,
                            v_isExporting_7836_,
                        );
                        if v___x_7839_ == 0 {
                            lean_dec_ref(v___x_7838_);
                            lean_dec_ref(v_env_7834_);
                            lean_dec(v_declHint_7830_);
                            v___x_7840_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_7840_, 0, v_msg_7829_);
                            return v___x_7840_;
                        } else {
                            v___x_7841_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
                            v___x_7842_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
                            v___x_7843_ = l_Lean_Options_empty;
                            v___x_7844_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_7844_, 0, v___x_7838_);
                            lean_ctor_set(v___x_7844_, 1, v___x_7841_);
                            lean_ctor_set(v___x_7844_, 2, v___x_7842_);
                            lean_ctor_set(v___x_7844_, 3, v___x_7843_);
                            lean_inc(v_declHint_7830_);
                            v___x_7845_ =
                                l_Lean_MessageData_ofConstName(v_declHint_7830_, v___x_7835_);
                            v_c_7846_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_7846_, 0, v___x_7844_);
                            lean_ctor_set(v_c_7846_, 1, v___x_7845_);
                            v___x_7847_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_7834_,
                                v_declHint_7830_,
                            );
                            if lean_obj_tag(v___x_7847_) == 0 {
                                lean_dec_ref(v_env_7834_);
                                lean_dec(v_declHint_7830_);
                                v___x_7848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
                                v___x_7849_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7849_, 0, v___x_7848_);
                                lean_ctor_set(v___x_7849_, 1, v_c_7846_);
                                v___x_7850_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
                                v___x_7851_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7851_, 0, v___x_7849_);
                                lean_ctor_set(v___x_7851_, 1, v___x_7850_);
                                v___x_7852_ = l_Lean_MessageData_note(v___x_7851_);
                                v___x_7853_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7853_, 0, v_msg_7829_);
                                lean_ctor_set(v___x_7853_, 1, v___x_7852_);
                                v___x_7854_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_7854_, 0, v___x_7853_);
                                return v___x_7854_;
                            } else {
                                v_val_7855_ = lean_ctor_get(v___x_7847_, 0);
                                v_isSharedCheck_7890_ = (!lean_is_exclusive(v___x_7847_)) as u8;
                                if v_isSharedCheck_7890_ == 0 {
                                    v___x_7857_ = v___x_7847_;
                                    v_isShared_7858_ = v_isSharedCheck_7890_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_7855_);
                                    lean_dec(v___x_7847_);
                                    v___x_7857_ = lean_box(0);
                                    v_isShared_7858_ = v_isSharedCheck_7890_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_7834_);
                    lean_dec(v_declHint_7830_);
                    v___x_7891_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7891_, 0, v_msg_7829_);
                    return v___x_7891_;
                }
            }
            1 => {
                v___x_7859_ = lean_box(0);
                v___x_7860_ = l_Lean_Environment_header(v_env_7834_);
                lean_dec_ref(v_env_7834_);
                v___x_7861_ = l_Lean_EnvironmentHeader_moduleNames(v___x_7860_);
                v_mod_7862_ = lean_array_get(v___x_7859_, v___x_7861_, v_val_7855_);
                lean_dec(v_val_7855_);
                lean_dec_ref(v___x_7861_);
                v___x_7863_ = l_Lean_isPrivateName(v_declHint_7830_);
                lean_dec(v_declHint_7830_);
                if v___x_7863_ == 0 {
                    v___x_7864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_7865_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7865_, 0, v___x_7864_);
                    lean_ctor_set(v___x_7865_, 1, v_c_7846_);
                    v___x_7866_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_7867_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7867_, 0, v___x_7865_);
                    lean_ctor_set(v___x_7867_, 1, v___x_7866_);
                    v___x_7868_ = l_Lean_MessageData_ofName(v_mod_7862_);
                    v___x_7869_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7869_, 0, v___x_7867_);
                    lean_ctor_set(v___x_7869_, 1, v___x_7868_);
                    v___x_7870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
                    v___x_7871_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7871_, 0, v___x_7869_);
                    lean_ctor_set(v___x_7871_, 1, v___x_7870_);
                    v___x_7872_ = l_Lean_MessageData_note(v___x_7871_);
                    v___x_7873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7873_, 0, v_msg_7829_);
                    lean_ctor_set(v___x_7873_, 1, v___x_7872_);
                    if v_isShared_7858_ == 0 {
                        lean_ctor_set_tag(v___x_7857_, 0);
                        lean_ctor_set(v___x_7857_, 0, v___x_7873_);
                        v___x_7875_ = v___x_7857_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7876_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7876_, 0, v___x_7873_);
                        v___x_7875_ = v_reuseFailAlloc_7876_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7877_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_7878_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7878_, 0, v___x_7877_);
                    lean_ctor_set(v___x_7878_, 1, v_c_7846_);
                    v___x_7879_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
                    v___x_7880_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7880_, 0, v___x_7878_);
                    lean_ctor_set(v___x_7880_, 1, v___x_7879_);
                    v___x_7881_ = l_Lean_MessageData_ofName(v_mod_7862_);
                    v___x_7882_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7882_, 0, v___x_7880_);
                    lean_ctor_set(v___x_7882_, 1, v___x_7881_);
                    v___x_7883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
                    v___x_7884_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7884_, 0, v___x_7882_);
                    lean_ctor_set(v___x_7884_, 1, v___x_7883_);
                    v___x_7885_ = l_Lean_MessageData_note(v___x_7884_);
                    v___x_7886_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7886_, 0, v_msg_7829_);
                    lean_ctor_set(v___x_7886_, 1, v___x_7885_);
                    if v_isShared_7858_ == 0 {
                        lean_ctor_set_tag(v___x_7857_, 0);
                        lean_ctor_set(v___x_7857_, 0, v___x_7886_);
                        v___x_7888_ = v___x_7857_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7889_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7889_, 0, v___x_7886_);
                        v___x_7888_ = v_reuseFailAlloc_7889_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7875_;
            }
            3 => {
                return v___x_7888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_7892_: *mut LeanObject,
    mut v_declHint_7893_: *mut LeanObject,
    mut v___y_7894_: *mut LeanObject,
    mut v___y_7895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7896_: *mut LeanObject = core::ptr::null_mut();
    v_res_7896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_7892_, v_declHint_7893_, v___y_7894_);
    lean_dec(v___y_7894_);
    return v_res_7896_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(
    mut v_msg_7897_: *mut LeanObject,
    mut v_declHint_7898_: *mut LeanObject,
    mut v___y_7899_: *mut LeanObject,
    mut v___y_7900_: *mut LeanObject,
    mut v___y_7901_: *mut LeanObject,
    mut v___y_7902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7908_: u8 = 0;
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7914_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7904_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_7897_, v_declHint_7898_, v___y_7902_);
                v_a_7905_ = lean_ctor_get(v___x_7904_, 0);
                v_isSharedCheck_7914_ = (!lean_is_exclusive(v___x_7904_)) as u8;
                if v_isSharedCheck_7914_ == 0 {
                    v___x_7907_ = v___x_7904_;
                    v_isShared_7908_ = v_isSharedCheck_7914_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7905_);
                    lean_dec(v___x_7904_);
                    v___x_7907_ = lean_box(0);
                    v_isShared_7908_ = v_isSharedCheck_7914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7909_ = l_Lean_unknownIdentifierMessageTag;
                v___x_7910_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_7910_, 0, v___x_7909_);
                lean_ctor_set(v___x_7910_, 1, v_a_7905_);
                if v_isShared_7908_ == 0 {
                    lean_ctor_set(v___x_7907_, 0, v___x_7910_);
                    v___x_7912_ = v___x_7907_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7913_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7913_, 0, v___x_7910_);
                    v___x_7912_ = v_reuseFailAlloc_7913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(
    mut v_msg_7915_: *mut LeanObject,
    mut v_declHint_7916_: *mut LeanObject,
    mut v___y_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
    mut v___y_7919_: *mut LeanObject,
    mut v___y_7920_: *mut LeanObject,
    mut v___y_7921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7922_: *mut LeanObject = core::ptr::null_mut();
    v_res_7922_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_7915_, v_declHint_7916_, v___y_7917_, v___y_7918_, v___y_7919_, v___y_7920_);
    lean_dec(v___y_7920_);
    lean_dec_ref(v___y_7919_);
    lean_dec(v___y_7918_);
    lean_dec_ref(v___y_7917_);
    return v_res_7922_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(
    mut v_ref_7923_: *mut LeanObject,
    mut v_msg_7924_: *mut LeanObject,
    mut v_declHint_7925_: *mut LeanObject,
    mut v___y_7926_: *mut LeanObject,
    mut v___y_7927_: *mut LeanObject,
    mut v___y_7928_: *mut LeanObject,
    mut v___y_7929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    v___x_7931_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_7924_, v_declHint_7925_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_);
    v_a_7932_ = lean_ctor_get(v___x_7931_, 0);
    lean_inc(v_a_7932_);
    lean_dec_ref(v___x_7931_);
    v___x_7933_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_7923_, v_a_7932_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_);
    return v___x_7933_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_ref_7934_: *mut LeanObject,
    mut v_msg_7935_: *mut LeanObject,
    mut v_declHint_7936_: *mut LeanObject,
    mut v___y_7937_: *mut LeanObject,
    mut v___y_7938_: *mut LeanObject,
    mut v___y_7939_: *mut LeanObject,
    mut v___y_7940_: *mut LeanObject,
    mut v___y_7941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7942_: *mut LeanObject = core::ptr::null_mut();
    v_res_7942_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_7934_, v_msg_7935_, v_declHint_7936_, v___y_7937_, v___y_7938_, v___y_7939_, v___y_7940_);
    lean_dec(v___y_7940_);
    lean_dec_ref(v___y_7939_);
    lean_dec(v___y_7938_);
    lean_dec_ref(v___y_7937_);
    lean_dec(v_ref_7934_);
    return v_res_7942_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    v___x_7944_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0;
    v___x_7945_ = l_Lean_stringToMessageData(v___x_7944_);
    return v___x_7945_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(
    mut v_ref_7946_: *mut LeanObject,
    mut v_constName_7947_: *mut LeanObject,
    mut v___y_7948_: *mut LeanObject,
    mut v___y_7949_: *mut LeanObject,
    mut v___y_7950_: *mut LeanObject,
    mut v___y_7951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: u8 = 0;
    let mut v___x_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    v___x_7953_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
    v___x_7954_ = 0;
    lean_inc(v_constName_7947_);
    v___x_7955_ = l_Lean_MessageData_ofConstName(v_constName_7947_, v___x_7954_);
    v___x_7956_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7956_, 0, v___x_7953_);
    lean_ctor_set(v___x_7956_, 1, v___x_7955_);
    v___x_7957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
    v___x_7958_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7958_, 0, v___x_7956_);
    lean_ctor_set(v___x_7958_, 1, v___x_7957_);
    v___x_7959_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_7946_, v___x_7958_, v_constName_7947_, v___y_7948_, v___y_7949_, v___y_7950_, v___y_7951_);
    return v___x_7959_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_ref_7960_: *mut LeanObject,
    mut v_constName_7961_: *mut LeanObject,
    mut v___y_7962_: *mut LeanObject,
    mut v___y_7963_: *mut LeanObject,
    mut v___y_7964_: *mut LeanObject,
    mut v___y_7965_: *mut LeanObject,
    mut v___y_7966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7967_: *mut LeanObject = core::ptr::null_mut();
    v_res_7967_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_7960_, v_constName_7961_, v___y_7962_, v___y_7963_, v___y_7964_, v___y_7965_);
    lean_dec(v___y_7965_);
    lean_dec_ref(v___y_7964_);
    lean_dec(v___y_7963_);
    lean_dec_ref(v___y_7962_);
    lean_dec(v_ref_7960_);
    return v_res_7967_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(
    mut v_constName_7968_: *mut LeanObject,
    mut v___y_7969_: *mut LeanObject,
    mut v___y_7970_: *mut LeanObject,
    mut v___y_7971_: *mut LeanObject,
    mut v___y_7972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    v_ref_7974_ = lean_ctor_get(v___y_7971_, 5);
    v___x_7975_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_7974_, v_constName_7968_, v___y_7969_, v___y_7970_, v___y_7971_, v___y_7972_);
    return v___x_7975_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(
    mut v_constName_7976_: *mut LeanObject,
    mut v___y_7977_: *mut LeanObject,
    mut v___y_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
    mut v___y_7980_: *mut LeanObject,
    mut v___y_7981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7982_: *mut LeanObject = core::ptr::null_mut();
    v_res_7982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_7976_, v___y_7977_, v___y_7978_, v___y_7979_, v___y_7980_);
    lean_dec(v___y_7980_);
    lean_dec_ref(v___y_7979_);
    lean_dec(v___y_7978_);
    lean_dec_ref(v___y_7977_);
    return v_res_7982_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(
    mut v_constName_7983_: *mut LeanObject,
    mut v___y_7984_: *mut LeanObject,
    mut v___y_7985_: *mut LeanObject,
    mut v___y_7986_: *mut LeanObject,
    mut v___y_7987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: u8 = 0;
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7997_: u8 = 0;
    let mut v___x_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7989_ = lean_st_ref_get(v___y_7987_);
                v_env_7990_ = lean_ctor_get(v___x_7989_, 0);
                lean_inc_ref(v_env_7990_);
                lean_dec(v___x_7989_);
                v___x_7991_ = 0;
                lean_inc(v_constName_7983_);
                v___x_7992_ =
                    l_Lean_Environment_find_x3f(v_env_7990_, v_constName_7983_, v___x_7991_);
                if lean_obj_tag(v___x_7992_) == 0 {
                    v___x_7993_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_7983_, v___y_7984_, v___y_7985_, v___y_7986_, v___y_7987_);
                    return v___x_7993_;
                } else {
                    lean_dec(v_constName_7983_);
                    v_val_7994_ = lean_ctor_get(v___x_7992_, 0);
                    v_isSharedCheck_8001_ = (!lean_is_exclusive(v___x_7992_)) as u8;
                    if v_isSharedCheck_8001_ == 0 {
                        v___x_7996_ = v___x_7992_;
                        v_isShared_7997_ = v_isSharedCheck_8001_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7994_);
                        lean_dec(v___x_7992_);
                        v___x_7996_ = lean_box(0);
                        v_isShared_7997_ = v_isSharedCheck_8001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7997_ == 0 {
                    lean_ctor_set_tag(v___x_7996_, 0);
                    v___x_7999_ = v___x_7996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8000_, 0, v_val_7994_);
                    v___x_7999_ = v_reuseFailAlloc_8000_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(
    mut v_constName_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
    mut v___y_8005_: *mut LeanObject,
    mut v___y_8006_: *mut LeanObject,
    mut v___y_8007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8008_: *mut LeanObject = core::ptr::null_mut();
    v_res_8008_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(
        v_constName_8002_,
        v___y_8003_,
        v___y_8004_,
        v___y_8005_,
        v___y_8006_,
    );
    lean_dec(v___y_8006_);
    lean_dec_ref(v___y_8005_);
    lean_dec(v___y_8004_);
    lean_dec_ref(v___y_8003_);
    return v_res_8008_;
}
pub unsafe fn l_Lean_Meta_mkCustomEliminator(
    mut v_elimName_8009_: *mut LeanObject,
    mut v_induction_8010_: u8,
    mut v_a_8011_: *mut LeanObject,
    mut v_a_8012_: *mut LeanObject,
    mut v_a_8013_: *mut LeanObject,
    mut v_a_8014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: u8 = 0;
    let mut v___x_8025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8029_: u8 = 0;
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8033_: u8 = 0;
    let mut v_a_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8037_: u8 = 0;
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8016_ = lean_box(0);
                lean_inc(v_elimName_8009_);
                v___x_8017_ = l_Lean_Meta_getElimInfo(
                    v_elimName_8009_,
                    v___x_8016_,
                    v_a_8011_,
                    v_a_8012_,
                    v_a_8013_,
                    v_a_8014_,
                );
                if lean_obj_tag(v___x_8017_) == 0 {
                    v_a_8018_ = lean_ctor_get(v___x_8017_, 0);
                    lean_inc(v_a_8018_);
                    lean_dec_ref_known(v___x_8017_, 1);
                    lean_inc(v_elimName_8009_);
                    v___x_8019_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(
                        v_elimName_8009_,
                        v_a_8011_,
                        v_a_8012_,
                        v_a_8013_,
                        v_a_8014_,
                    );
                    if lean_obj_tag(v___x_8019_) == 0 {
                        v_a_8020_ = lean_ctor_get(v___x_8019_, 0);
                        lean_inc(v_a_8020_);
                        lean_dec_ref_known(v___x_8019_, 1);
                        v___x_8021_ = lean_box((v_induction_8010_) as usize);
                        v___f_8022_ = lean_alloc_closure(
                            l_Lean_Meta_mkCustomEliminator___lam__0___boxed
                                as *mut core::ffi::c_void,
                            10,
                            3,
                        );
                        lean_closure_set(v___f_8022_, 0, v_a_8018_);
                        lean_closure_set(v___f_8022_, 1, v___x_8021_);
                        lean_closure_set(v___f_8022_, 2, v_elimName_8009_);
                        v___x_8023_ = l_Lean_ConstantInfo_type(v_a_8020_);
                        lean_dec(v_a_8020_);
                        v___x_8024_ = 0;
                        v___x_8025_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_8023_, v___f_8022_, v___x_8024_, v___x_8024_, v_a_8011_, v_a_8012_, v_a_8013_, v_a_8014_);
                        return v___x_8025_;
                    } else {
                        lean_dec(v_a_8018_);
                        lean_dec(v_elimName_8009_);
                        v_a_8026_ = lean_ctor_get(v___x_8019_, 0);
                        v_isSharedCheck_8033_ = (!lean_is_exclusive(v___x_8019_)) as u8;
                        if v_isSharedCheck_8033_ == 0 {
                            v___x_8028_ = v___x_8019_;
                            v_isShared_8029_ = v_isSharedCheck_8033_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8026_);
                            lean_dec(v___x_8019_);
                            v___x_8028_ = lean_box(0);
                            v_isShared_8029_ = v_isSharedCheck_8033_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_elimName_8009_);
                    v_a_8034_ = lean_ctor_get(v___x_8017_, 0);
                    v_isSharedCheck_8041_ = (!lean_is_exclusive(v___x_8017_)) as u8;
                    if v_isSharedCheck_8041_ == 0 {
                        v___x_8036_ = v___x_8017_;
                        v_isShared_8037_ = v_isSharedCheck_8041_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8034_);
                        lean_dec(v___x_8017_);
                        v___x_8036_ = lean_box(0);
                        v_isShared_8037_ = v_isSharedCheck_8041_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8029_ == 0 {
                    v___x_8031_ = v___x_8028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8032_, 0, v_a_8026_);
                    v___x_8031_ = v_reuseFailAlloc_8032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8031_;
            }
            3 => {
                if v_isShared_8037_ == 0 {
                    v___x_8039_ = v___x_8036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8040_, 0, v_a_8034_);
                    v___x_8039_ = v_reuseFailAlloc_8040_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkCustomEliminator___boxed(
    mut v_elimName_8042_: *mut LeanObject,
    mut v_induction_8043_: *mut LeanObject,
    mut v_a_8044_: *mut LeanObject,
    mut v_a_8045_: *mut LeanObject,
    mut v_a_8046_: *mut LeanObject,
    mut v_a_8047_: *mut LeanObject,
    mut v_a_8048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_induction_boxed_8049_: u8 = 0;
    let mut v_res_8050_: *mut LeanObject = core::ptr::null_mut();
    v_induction_boxed_8049_ = (lean_unbox(v_induction_8043_) as u8);
    v_res_8050_ = l_Lean_Meta_mkCustomEliminator(
        v_elimName_8042_,
        v_induction_boxed_8049_,
        v_a_8044_,
        v_a_8045_,
        v_a_8046_,
        v_a_8047_,
    );
    lean_dec(v_a_8047_);
    lean_dec_ref(v_a_8046_);
    lean_dec(v_a_8045_);
    lean_dec_ref(v_a_8044_);
    return v_res_8050_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(
    mut v_upperBound_8051_: *mut LeanObject,
    mut v___x_8052_: *mut LeanObject,
    mut v_xs_8053_: *mut LeanObject,
    mut v___x_8054_: *mut LeanObject,
    mut v_inst_8055_: *mut LeanObject,
    mut v_R_8056_: *mut LeanObject,
    mut v_a_8057_: *mut LeanObject,
    mut v_b_8058_: *mut LeanObject,
    mut v_c_8059_: *mut LeanObject,
    mut v___y_8060_: *mut LeanObject,
    mut v___y_8061_: *mut LeanObject,
    mut v___y_8062_: *mut LeanObject,
    mut v___y_8063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    v___x_8065_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(
            v_upperBound_8051_,
            v___x_8052_,
            v_xs_8053_,
            v___x_8054_,
            v_a_8057_,
            v_b_8058_,
            v___y_8060_,
            v___y_8061_,
            v___y_8062_,
            v___y_8063_,
        );
    return v___x_8065_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(
    mut v_upperBound_8066_: *mut LeanObject,
    mut v___x_8067_: *mut LeanObject,
    mut v_xs_8068_: *mut LeanObject,
    mut v___x_8069_: *mut LeanObject,
    mut v_inst_8070_: *mut LeanObject,
    mut v_R_8071_: *mut LeanObject,
    mut v_a_8072_: *mut LeanObject,
    mut v_b_8073_: *mut LeanObject,
    mut v_c_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
    mut v___y_8076_: *mut LeanObject,
    mut v___y_8077_: *mut LeanObject,
    mut v___y_8078_: *mut LeanObject,
    mut v___y_8079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8080_: *mut LeanObject = core::ptr::null_mut();
    v_res_8080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(
        v_upperBound_8066_,
        v___x_8067_,
        v_xs_8068_,
        v___x_8069_,
        v_inst_8070_,
        v_R_8071_,
        v_a_8072_,
        v_b_8073_,
        v_c_8074_,
        v___y_8075_,
        v___y_8076_,
        v___y_8077_,
        v___y_8078_,
    );
    lean_dec(v___y_8078_);
    lean_dec_ref(v___y_8077_);
    lean_dec(v___y_8076_);
    lean_dec_ref(v___y_8075_);
    lean_dec_ref(v___x_8069_);
    lean_dec_ref(v_xs_8068_);
    lean_dec_ref(v___x_8067_);
    lean_dec(v_upperBound_8066_);
    return v_res_8080_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(
    mut v_upperBound_8081_: *mut LeanObject,
    mut v___x_8082_: *mut LeanObject,
    mut v___x_8083_: *mut LeanObject,
    mut v_xs_8084_: *mut LeanObject,
    mut v_inst_8085_: *mut LeanObject,
    mut v_R_8086_: *mut LeanObject,
    mut v_a_8087_: *mut LeanObject,
    mut v_b_8088_: *mut LeanObject,
    mut v_c_8089_: *mut LeanObject,
    mut v___y_8090_: *mut LeanObject,
    mut v___y_8091_: *mut LeanObject,
    mut v___y_8092_: *mut LeanObject,
    mut v___y_8093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8095_: *mut LeanObject = core::ptr::null_mut();
    v___x_8095_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(
            v_upperBound_8081_,
            v___x_8082_,
            v___x_8083_,
            v_xs_8084_,
            v_a_8087_,
            v_b_8088_,
            v___y_8090_,
            v___y_8091_,
            v___y_8092_,
            v___y_8093_,
        );
    return v___x_8095_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(
    mut v_upperBound_8096_: *mut LeanObject,
    mut v___x_8097_: *mut LeanObject,
    mut v___x_8098_: *mut LeanObject,
    mut v_xs_8099_: *mut LeanObject,
    mut v_inst_8100_: *mut LeanObject,
    mut v_R_8101_: *mut LeanObject,
    mut v_a_8102_: *mut LeanObject,
    mut v_b_8103_: *mut LeanObject,
    mut v_c_8104_: *mut LeanObject,
    mut v___y_8105_: *mut LeanObject,
    mut v___y_8106_: *mut LeanObject,
    mut v___y_8107_: *mut LeanObject,
    mut v___y_8108_: *mut LeanObject,
    mut v___y_8109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8110_: *mut LeanObject = core::ptr::null_mut();
    v_res_8110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(
        v_upperBound_8096_,
        v___x_8097_,
        v___x_8098_,
        v_xs_8099_,
        v_inst_8100_,
        v_R_8101_,
        v_a_8102_,
        v_b_8103_,
        v_c_8104_,
        v___y_8105_,
        v___y_8106_,
        v___y_8107_,
        v___y_8108_,
    );
    lean_dec(v___y_8108_);
    lean_dec_ref(v___y_8107_);
    lean_dec(v___y_8106_);
    lean_dec_ref(v___y_8105_);
    lean_dec_ref(v_xs_8099_);
    lean_dec_ref(v___x_8098_);
    lean_dec(v___x_8097_);
    lean_dec(v_upperBound_8096_);
    return v_res_8110_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(
    mut v_00_u03b1_8111_: *mut LeanObject,
    mut v_constName_8112_: *mut LeanObject,
    mut v___y_8113_: *mut LeanObject,
    mut v___y_8114_: *mut LeanObject,
    mut v___y_8115_: *mut LeanObject,
    mut v___y_8116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    v___x_8118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_8112_, v___y_8113_, v___y_8114_, v___y_8115_, v___y_8116_);
    return v___x_8118_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(
    mut v_00_u03b1_8119_: *mut LeanObject,
    mut v_constName_8120_: *mut LeanObject,
    mut v___y_8121_: *mut LeanObject,
    mut v___y_8122_: *mut LeanObject,
    mut v___y_8123_: *mut LeanObject,
    mut v___y_8124_: *mut LeanObject,
    mut v___y_8125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8126_: *mut LeanObject = core::ptr::null_mut();
    v_res_8126_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_8119_, v_constName_8120_, v___y_8121_, v___y_8122_, v___y_8123_, v___y_8124_);
    lean_dec(v___y_8124_);
    lean_dec_ref(v___y_8123_);
    lean_dec(v___y_8122_);
    lean_dec_ref(v___y_8121_);
    return v_res_8126_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(
    mut v_00_u03b1_8127_: *mut LeanObject,
    mut v_ref_8128_: *mut LeanObject,
    mut v_constName_8129_: *mut LeanObject,
    mut v___y_8130_: *mut LeanObject,
    mut v___y_8131_: *mut LeanObject,
    mut v___y_8132_: *mut LeanObject,
    mut v___y_8133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8135_: *mut LeanObject = core::ptr::null_mut();
    v___x_8135_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_8128_, v_constName_8129_, v___y_8130_, v___y_8131_, v___y_8132_, v___y_8133_);
    return v___x_8135_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b1_8136_: *mut LeanObject,
    mut v_ref_8137_: *mut LeanObject,
    mut v_constName_8138_: *mut LeanObject,
    mut v___y_8139_: *mut LeanObject,
    mut v___y_8140_: *mut LeanObject,
    mut v___y_8141_: *mut LeanObject,
    mut v___y_8142_: *mut LeanObject,
    mut v___y_8143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8144_: *mut LeanObject = core::ptr::null_mut();
    v_res_8144_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_8136_, v_ref_8137_, v_constName_8138_, v___y_8139_, v___y_8140_, v___y_8141_, v___y_8142_);
    lean_dec(v___y_8142_);
    lean_dec_ref(v___y_8141_);
    lean_dec(v___y_8140_);
    lean_dec_ref(v___y_8139_);
    lean_dec(v_ref_8137_);
    return v_res_8144_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(
    mut v_00_u03b1_8145_: *mut LeanObject,
    mut v_ref_8146_: *mut LeanObject,
    mut v_msg_8147_: *mut LeanObject,
    mut v_declHint_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
    mut v___y_8150_: *mut LeanObject,
    mut v___y_8151_: *mut LeanObject,
    mut v___y_8152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    v___x_8154_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_8146_, v_msg_8147_, v_declHint_8148_, v___y_8149_, v___y_8150_, v___y_8151_, v___y_8152_);
    return v___x_8154_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(
    mut v_00_u03b1_8155_: *mut LeanObject,
    mut v_ref_8156_: *mut LeanObject,
    mut v_msg_8157_: *mut LeanObject,
    mut v_declHint_8158_: *mut LeanObject,
    mut v___y_8159_: *mut LeanObject,
    mut v___y_8160_: *mut LeanObject,
    mut v___y_8161_: *mut LeanObject,
    mut v___y_8162_: *mut LeanObject,
    mut v___y_8163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8164_: *mut LeanObject = core::ptr::null_mut();
    v_res_8164_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_8155_, v_ref_8156_, v_msg_8157_, v_declHint_8158_, v___y_8159_, v___y_8160_, v___y_8161_, v___y_8162_);
    lean_dec(v___y_8162_);
    lean_dec_ref(v___y_8161_);
    lean_dec(v___y_8160_);
    lean_dec_ref(v___y_8159_);
    lean_dec(v_ref_8156_);
    return v_res_8164_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(
    mut v_msg_8165_: *mut LeanObject,
    mut v_declHint_8166_: *mut LeanObject,
    mut v___y_8167_: *mut LeanObject,
    mut v___y_8168_: *mut LeanObject,
    mut v___y_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8172_: *mut LeanObject = core::ptr::null_mut();
    v___x_8172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_8165_, v_declHint_8166_, v___y_8170_);
    return v___x_8172_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(
    mut v_msg_8173_: *mut LeanObject,
    mut v_declHint_8174_: *mut LeanObject,
    mut v___y_8175_: *mut LeanObject,
    mut v___y_8176_: *mut LeanObject,
    mut v___y_8177_: *mut LeanObject,
    mut v___y_8178_: *mut LeanObject,
    mut v___y_8179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8180_: *mut LeanObject = core::ptr::null_mut();
    v_res_8180_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_8173_, v_declHint_8174_, v___y_8175_, v___y_8176_, v___y_8177_, v___y_8178_);
    lean_dec(v___y_8178_);
    lean_dec_ref(v___y_8177_);
    lean_dec(v___y_8176_);
    lean_dec_ref(v___y_8175_);
    return v_res_8180_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(
    mut v_00_u03b1_8181_: *mut LeanObject,
    mut v_ref_8182_: *mut LeanObject,
    mut v_msg_8183_: *mut LeanObject,
    mut v___y_8184_: *mut LeanObject,
    mut v___y_8185_: *mut LeanObject,
    mut v___y_8186_: *mut LeanObject,
    mut v___y_8187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    v___x_8189_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_8182_, v_msg_8183_, v___y_8184_, v___y_8185_, v___y_8186_, v___y_8187_);
    return v___x_8189_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(
    mut v_00_u03b1_8190_: *mut LeanObject,
    mut v_ref_8191_: *mut LeanObject,
    mut v_msg_8192_: *mut LeanObject,
    mut v___y_8193_: *mut LeanObject,
    mut v___y_8194_: *mut LeanObject,
    mut v___y_8195_: *mut LeanObject,
    mut v___y_8196_: *mut LeanObject,
    mut v___y_8197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8198_: *mut LeanObject = core::ptr::null_mut();
    v_res_8198_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_8190_, v_ref_8191_, v_msg_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_);
    lean_dec(v___y_8196_);
    lean_dec_ref(v___y_8195_);
    lean_dec(v___y_8194_);
    lean_dec_ref(v___y_8193_);
    lean_dec(v_ref_8191_);
    return v_res_8198_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_8199_: *mut LeanObject = core::ptr::null_mut();
    v___x_8199_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_8199_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8201_: *mut LeanObject = core::ptr::null_mut();
    v___x_8200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
    v___x_8201_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8201_, 0, v___x_8200_);
    return v___x_8201_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut LeanObject = core::ptr::null_mut();
    v___x_8202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
    v___x_8203_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8203_, 0, v___x_8202_);
    lean_ctor_set(v___x_8203_, 1, v___x_8202_);
    return v___x_8203_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_8204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8205_: *mut LeanObject = core::ptr::null_mut();
    v___x_8204_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
    v___x_8205_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_8205_, 0, v___x_8204_);
    lean_ctor_set(v___x_8205_, 1, v___x_8204_);
    lean_ctor_set(v___x_8205_, 2, v___x_8204_);
    lean_ctor_set(v___x_8205_, 3, v___x_8204_);
    lean_ctor_set(v___x_8205_, 4, v___x_8204_);
    lean_ctor_set(v___x_8205_, 5, v___x_8204_);
    return v___x_8205_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(
    mut v_ext_8206_: *mut LeanObject,
    mut v_b_8207_: *mut LeanObject,
    mut v_kind_8208_: u8,
    mut v___y_8209_: *mut LeanObject,
    mut v___y_8210_: *mut LeanObject,
    mut v___y_8211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_8213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_8217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8225_: u8 = 0;
    let mut v___x_8226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_8232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8238_: u8 = 0;
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8246_: u8 = 0;
    let mut v_unused_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8249_: u8 = 0;
    let mut v_unused_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_8213_ = lean_ctor_get(v___y_8210_, 6);
                v___x_8214_ = lean_st_ref_take(v___y_8211_);
                v_env_8215_ = lean_ctor_get(v___x_8214_, 0);
                v_nextMacroScope_8216_ = lean_ctor_get(v___x_8214_, 1);
                v_ngen_8217_ = lean_ctor_get(v___x_8214_, 2);
                v_auxDeclNGen_8218_ = lean_ctor_get(v___x_8214_, 3);
                v_traceState_8219_ = lean_ctor_get(v___x_8214_, 4);
                v_messages_8220_ = lean_ctor_get(v___x_8214_, 6);
                v_infoState_8221_ = lean_ctor_get(v___x_8214_, 7);
                v_snapshotTasks_8222_ = lean_ctor_get(v___x_8214_, 8);
                v_isSharedCheck_8249_ = (!lean_is_exclusive(v___x_8214_)) as u8;
                if v_isSharedCheck_8249_ == 0 {
                    v_unused_8250_ = lean_ctor_get(v___x_8214_, 5);
                    lean_dec(v_unused_8250_);
                    v___x_8224_ = v___x_8214_;
                    v_isShared_8225_ = v_isSharedCheck_8249_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_8222_);
                    lean_inc(v_infoState_8221_);
                    lean_inc(v_messages_8220_);
                    lean_inc(v_traceState_8219_);
                    lean_inc(v_auxDeclNGen_8218_);
                    lean_inc(v_ngen_8217_);
                    lean_inc(v_nextMacroScope_8216_);
                    lean_inc(v_env_8215_);
                    lean_dec(v___x_8214_);
                    v___x_8224_ = lean_box(0);
                    v_isShared_8225_ = v_isSharedCheck_8249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_8213_);
                v___x_8226_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_8215_,
                    v_ext_8206_,
                    v_b_8207_,
                    v_kind_8208_,
                    v_currNamespace_8213_,
                );
                v___x_8227_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
                if v_isShared_8225_ == 0 {
                    lean_ctor_set(v___x_8224_, 5, v___x_8227_);
                    lean_ctor_set(v___x_8224_, 0, v___x_8226_);
                    v___x_8229_ = v___x_8224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8248_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 0, v___x_8226_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 1, v_nextMacroScope_8216_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 2, v_ngen_8217_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 3, v_auxDeclNGen_8218_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 4, v_traceState_8219_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 5, v___x_8227_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 6, v_messages_8220_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 7, v_infoState_8221_);
                    lean_ctor_set(v_reuseFailAlloc_8248_, 8, v_snapshotTasks_8222_);
                    v___x_8229_ = v_reuseFailAlloc_8248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8230_ = lean_st_ref_set(v___y_8211_, v___x_8229_);
                v___x_8231_ = lean_st_ref_take(v___y_8209_);
                v_mctx_8232_ = lean_ctor_get(v___x_8231_, 0);
                v_zetaDeltaFVarIds_8233_ = lean_ctor_get(v___x_8231_, 2);
                v_postponed_8234_ = lean_ctor_get(v___x_8231_, 3);
                v_diag_8235_ = lean_ctor_get(v___x_8231_, 4);
                v_isSharedCheck_8246_ = (!lean_is_exclusive(v___x_8231_)) as u8;
                if v_isSharedCheck_8246_ == 0 {
                    v_unused_8247_ = lean_ctor_get(v___x_8231_, 1);
                    lean_dec(v_unused_8247_);
                    v___x_8237_ = v___x_8231_;
                    v_isShared_8238_ = v_isSharedCheck_8246_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_8235_);
                    lean_inc(v_postponed_8234_);
                    lean_inc(v_zetaDeltaFVarIds_8233_);
                    lean_inc(v_mctx_8232_);
                    lean_dec(v___x_8231_);
                    v___x_8237_ = lean_box(0);
                    v_isShared_8238_ = v_isSharedCheck_8246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8239_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
                if v_isShared_8238_ == 0 {
                    lean_ctor_set(v___x_8237_, 1, v___x_8239_);
                    v___x_8241_ = v___x_8237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8245_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8245_, 0, v_mctx_8232_);
                    lean_ctor_set(v_reuseFailAlloc_8245_, 1, v___x_8239_);
                    lean_ctor_set(v_reuseFailAlloc_8245_, 2, v_zetaDeltaFVarIds_8233_);
                    lean_ctor_set(v_reuseFailAlloc_8245_, 3, v_postponed_8234_);
                    lean_ctor_set(v_reuseFailAlloc_8245_, 4, v_diag_8235_);
                    v___x_8241_ = v_reuseFailAlloc_8245_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8242_ = lean_st_ref_set(v___y_8209_, v___x_8241_);
                v___x_8243_ = lean_box(0);
                v___x_8244_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8244_, 0, v___x_8243_);
                return v___x_8244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(
    mut v_ext_8251_: *mut LeanObject,
    mut v_b_8252_: *mut LeanObject,
    mut v_kind_8253_: *mut LeanObject,
    mut v___y_8254_: *mut LeanObject,
    mut v___y_8255_: *mut LeanObject,
    mut v___y_8256_: *mut LeanObject,
    mut v___y_8257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8258_: u8 = 0;
    let mut v_res_8259_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8258_ = (lean_unbox(v_kind_8253_) as u8);
    v_res_8259_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(
            v_ext_8251_,
            v_b_8252_,
            v_kind_boxed_8258_,
            v___y_8254_,
            v___y_8255_,
            v___y_8256_,
        );
    lean_dec(v___y_8256_);
    lean_dec_ref(v___y_8255_);
    lean_dec(v___y_8254_);
    return v_res_8259_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(
    mut v_00_u03b1_8260_: *mut LeanObject,
    mut v_00_u03b2_8261_: *mut LeanObject,
    mut v_00_u03c3_8262_: *mut LeanObject,
    mut v_ext_8263_: *mut LeanObject,
    mut v_b_8264_: *mut LeanObject,
    mut v_kind_8265_: u8,
    mut v___y_8266_: *mut LeanObject,
    mut v___y_8267_: *mut LeanObject,
    mut v___y_8268_: *mut LeanObject,
    mut v___y_8269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    v___x_8271_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(
            v_ext_8263_,
            v_b_8264_,
            v_kind_8265_,
            v___y_8267_,
            v___y_8268_,
            v___y_8269_,
        );
    return v___x_8271_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(
    mut v_00_u03b1_8272_: *mut LeanObject,
    mut v_00_u03b2_8273_: *mut LeanObject,
    mut v_00_u03c3_8274_: *mut LeanObject,
    mut v_ext_8275_: *mut LeanObject,
    mut v_b_8276_: *mut LeanObject,
    mut v_kind_8277_: *mut LeanObject,
    mut v___y_8278_: *mut LeanObject,
    mut v___y_8279_: *mut LeanObject,
    mut v___y_8280_: *mut LeanObject,
    mut v___y_8281_: *mut LeanObject,
    mut v___y_8282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8283_: u8 = 0;
    let mut v_res_8284_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8283_ = (lean_unbox(v_kind_8277_) as u8);
    v_res_8284_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(
        v_00_u03b1_8272_,
        v_00_u03b2_8273_,
        v_00_u03c3_8274_,
        v_ext_8275_,
        v_b_8276_,
        v_kind_boxed_8283_,
        v___y_8278_,
        v___y_8279_,
        v___y_8280_,
        v___y_8281_,
    );
    lean_dec(v___y_8281_);
    lean_dec_ref(v___y_8280_);
    lean_dec(v___y_8279_);
    lean_dec_ref(v___y_8278_);
    return v_res_8284_;
}
pub unsafe fn l_Lean_Meta_addCustomEliminator(
    mut v_declName_8285_: *mut LeanObject,
    mut v_attrKind_8286_: u8,
    mut v_induction_8287_: u8,
    mut v_a_8288_: *mut LeanObject,
    mut v_a_8289_: *mut LeanObject,
    mut v_a_8290_: *mut LeanObject,
    mut v_a_8291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8300_: u8 = 0;
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8293_ = l_Lean_Meta_mkCustomEliminator(
                    v_declName_8285_,
                    v_induction_8287_,
                    v_a_8288_,
                    v_a_8289_,
                    v_a_8290_,
                    v_a_8291_,
                );
                if lean_obj_tag(v___x_8293_) == 0 {
                    v_a_8294_ = lean_ctor_get(v___x_8293_, 0);
                    lean_inc(v_a_8294_);
                    lean_dec_ref_known(v___x_8293_, 1);
                    v___x_8295_ = l_Lean_Meta_customEliminatorExt;
                    v___x_8296_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_8295_, v_a_8294_, v_attrKind_8286_, v_a_8289_, v_a_8290_, v_a_8291_);
                    return v___x_8296_;
                } else {
                    v_a_8297_ = lean_ctor_get(v___x_8293_, 0);
                    v_isSharedCheck_8304_ = (!lean_is_exclusive(v___x_8293_)) as u8;
                    if v_isSharedCheck_8304_ == 0 {
                        v___x_8299_ = v___x_8293_;
                        v_isShared_8300_ = v_isSharedCheck_8304_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8297_);
                        lean_dec(v___x_8293_);
                        v___x_8299_ = lean_box(0);
                        v_isShared_8300_ = v_isSharedCheck_8304_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8300_ == 0 {
                    v___x_8302_ = v___x_8299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8303_, 0, v_a_8297_);
                    v___x_8302_ = v_reuseFailAlloc_8303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addCustomEliminator___boxed(
    mut v_declName_8305_: *mut LeanObject,
    mut v_attrKind_8306_: *mut LeanObject,
    mut v_induction_8307_: *mut LeanObject,
    mut v_a_8308_: *mut LeanObject,
    mut v_a_8309_: *mut LeanObject,
    mut v_a_8310_: *mut LeanObject,
    mut v_a_8311_: *mut LeanObject,
    mut v_a_8312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_8313_: u8 = 0;
    let mut v_induction_boxed_8314_: u8 = 0;
    let mut v_res_8315_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_8313_ = (lean_unbox(v_attrKind_8306_) as u8);
    v_induction_boxed_8314_ = (lean_unbox(v_induction_8307_) as u8);
    v_res_8315_ = l_Lean_Meta_addCustomEliminator(
        v_declName_8305_,
        v_attrKind_boxed_8313_,
        v_induction_boxed_8314_,
        v_a_8308_,
        v_a_8309_,
        v_a_8310_,
        v_a_8311_,
    );
    lean_dec(v_a_8311_);
    lean_dec_ref(v_a_8310_);
    lean_dec(v_a_8309_);
    lean_dec_ref(v_a_8308_);
    return v_res_8315_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_8322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: u64 = 0;
    v___x_8322_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8323_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_8322_);
    return v___x_8323_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8324_: u64 = 0;
    let mut v___x_8325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    v___x_8324_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8325_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8326_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_8326_, 0, v___x_8325_);
    lean_ctor_set_uint64(
        v___x_8326_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_8324_,
    );
    return v___x_8326_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8327_: *mut LeanObject = core::ptr::null_mut();
    v___x_8327_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_8327_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8329_: *mut LeanObject = core::ptr::null_mut();
    v___x_8328_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8329_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8329_, 0, v___x_8328_);
    return v___x_8329_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    v___x_8330_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8331_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_8331_, 0, v___x_8330_);
    lean_ctor_set(v___x_8331_, 1, v___x_8330_);
    lean_ctor_set(v___x_8331_, 2, v___x_8330_);
    lean_ctor_set(v___x_8331_, 3, v___x_8330_);
    lean_ctor_set(v___x_8331_, 4, v___x_8330_);
    lean_ctor_set(v___x_8331_, 5, v___x_8330_);
    return v___x_8331_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8333_: *mut LeanObject = core::ptr::null_mut();
    v___x_8332_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8333_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_8333_, 0, v___x_8332_);
    lean_ctor_set(v___x_8333_, 1, v___x_8332_);
    lean_ctor_set(v___x_8333_, 2, v___x_8332_);
    lean_ctor_set(v___x_8333_, 3, v___x_8332_);
    lean_ctor_set(v___x_8333_, 4, v___x_8332_);
    return v___x_8333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(
    mut v___x_8334_: *mut LeanObject,
    mut v___x_8335_: *mut LeanObject,
    mut v_declName_8336_: *mut LeanObject,
    mut v_x_8337_: *mut LeanObject,
    mut v_attrKind_8338_: u8,
    mut v___y_8339_: *mut LeanObject,
    mut v___y_8340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8342_: u8 = 0;
    let mut v___x_8343_: u8 = 0;
    let mut v___x_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8349_: usize = 0;
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8364_: u8 = 0;
    let mut v___x_8365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8370_: u8 = 0;
    let mut v_unused_8371_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8342_ = 1;
                v___x_8343_ = 0;
                v___x_8344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8345_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8346_ = lean_unsigned_to_nat(32);
                v___x_8347_ = lean_mk_empty_array_with_capacity(v___x_8346_);
                v___x_8348_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
                v___x_8349_ = 5usize;
                lean_inc_n(v___x_8334_, 6);
                v___x_8350_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_8350_, 0, v___x_8348_);
                lean_ctor_set(v___x_8350_, 1, v___x_8347_);
                lean_ctor_set(v___x_8350_, 2, v___x_8334_);
                lean_ctor_set(v___x_8350_, 3, v___x_8334_);
                lean_ctor_set_usize(v___x_8350_, 4, v___x_8349_);
                v___x_8351_ = lean_box(1);
                lean_inc_ref(v___x_8350_);
                v___x_8352_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_8352_, 0, v___x_8345_);
                lean_ctor_set(v___x_8352_, 1, v___x_8350_);
                lean_ctor_set(v___x_8352_, 2, v___x_8351_);
                v___x_8353_ = lean_mk_empty_array_with_capacity(v___x_8334_);
                v___x_8354_ = lean_box(0);
                lean_inc(v___x_8335_);
                v___x_8355_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_8355_, 0, v___x_8344_);
                lean_ctor_set(v___x_8355_, 1, v___x_8335_);
                lean_ctor_set(v___x_8355_, 2, v___x_8352_);
                lean_ctor_set(v___x_8355_, 3, v___x_8353_);
                lean_ctor_set(v___x_8355_, 4, v___x_8354_);
                lean_ctor_set(v___x_8355_, 5, v___x_8334_);
                lean_ctor_set(v___x_8355_, 6, v___x_8354_);
                lean_ctor_set_uint8(
                    v___x_8355_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_8343_,
                );
                lean_ctor_set_uint8(
                    v___x_8355_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_8343_,
                );
                lean_ctor_set_uint8(
                    v___x_8355_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_8343_,
                );
                lean_ctor_set_uint8(
                    v___x_8355_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_8342_,
                );
                v___x_8356_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_8356_, 0, v___x_8334_);
                lean_ctor_set(v___x_8356_, 1, v___x_8334_);
                lean_ctor_set(v___x_8356_, 2, v___x_8334_);
                lean_ctor_set(v___x_8356_, 3, v___x_8334_);
                lean_ctor_set(v___x_8356_, 4, v___x_8345_);
                lean_ctor_set(v___x_8356_, 5, v___x_8345_);
                lean_ctor_set(v___x_8356_, 6, v___x_8345_);
                lean_ctor_set(v___x_8356_, 7, v___x_8345_);
                lean_ctor_set(v___x_8356_, 8, v___x_8345_);
                lean_ctor_set(v___x_8356_, 9, v___x_8345_);
                v___x_8357_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8358_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8359_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_8359_, 0, v___x_8356_);
                lean_ctor_set(v___x_8359_, 1, v___x_8357_);
                lean_ctor_set(v___x_8359_, 2, v___x_8335_);
                lean_ctor_set(v___x_8359_, 3, v___x_8350_);
                lean_ctor_set(v___x_8359_, 4, v___x_8358_);
                v___x_8360_ = lean_st_mk_ref(v___x_8359_);
                v___x_8361_ = l_Lean_Meta_addCustomEliminator(
                    v_declName_8336_,
                    v_attrKind_8338_,
                    v___x_8342_,
                    v___x_8355_,
                    v___x_8360_,
                    v___y_8339_,
                    v___y_8340_,
                );
                lean_dec_ref_known(v___x_8355_, 7);
                if lean_obj_tag(v___x_8361_) == 0 {
                    v_isSharedCheck_8370_ = (!lean_is_exclusive(v___x_8361_)) as u8;
                    if v_isSharedCheck_8370_ == 0 {
                        v_unused_8371_ = lean_ctor_get(v___x_8361_, 0);
                        lean_dec(v_unused_8371_);
                        v___x_8363_ = v___x_8361_;
                        v_isShared_8364_ = v_isSharedCheck_8370_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_8361_);
                        v___x_8363_ = lean_box(0);
                        v_isShared_8364_ = v_isSharedCheck_8370_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_8360_);
                    return v___x_8361_;
                }
            }
            1 => {
                v___x_8365_ = lean_st_ref_get(v___x_8360_);
                lean_dec(v___x_8360_);
                lean_dec(v___x_8365_);
                v___x_8366_ = lean_box(0);
                if v_isShared_8364_ == 0 {
                    lean_ctor_set(v___x_8363_, 0, v___x_8366_);
                    v___x_8368_ = v___x_8363_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8369_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8369_, 0, v___x_8366_);
                    v___x_8368_ = v_reuseFailAlloc_8369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(
    mut v___x_8372_: *mut LeanObject,
    mut v___x_8373_: *mut LeanObject,
    mut v_declName_8374_: *mut LeanObject,
    mut v_x_8375_: *mut LeanObject,
    mut v_attrKind_8376_: *mut LeanObject,
    mut v___y_8377_: *mut LeanObject,
    mut v___y_8378_: *mut LeanObject,
    mut v___y_8379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_8380_: u8 = 0;
    let mut v_res_8381_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_8380_ = (lean_unbox(v_attrKind_8376_) as u8);
    v_res_8381_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_8372_, v___x_8373_, v_declName_8374_, v_x_8375_, v_attrKind_boxed_8380_, v___y_8377_, v___y_8378_);
    lean_dec(v___y_8378_);
    lean_dec_ref(v___y_8377_);
    lean_dec(v_x_8375_);
    return v_res_8381_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_8382_: *mut LeanObject,
    mut v___y_8383_: *mut LeanObject,
    mut v___y_8384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_8388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8395_: *mut LeanObject = core::ptr::null_mut();
    v___x_8386_ = lean_st_ref_get(v___y_8384_);
    v_env_8387_ = lean_ctor_get(v___x_8386_, 0);
    lean_inc_ref(v_env_8387_);
    lean_dec(v___x_8386_);
    v_options_8388_ = lean_ctor_get(v___y_8383_, 2);
    v___x_8389_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
    v___x_8390_ = lean_unsigned_to_nat(32);
    v___x_8391_ = lean_mk_empty_array_with_capacity(v___x_8390_);
    lean_dec_ref(v___x_8391_);
    v___x_8392_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
    lean_inc_ref(v_options_8388_);
    v___x_8393_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_8393_, 0, v_env_8387_);
    lean_ctor_set(v___x_8393_, 1, v___x_8389_);
    lean_ctor_set(v___x_8393_, 2, v___x_8392_);
    lean_ctor_set(v___x_8393_, 3, v_options_8388_);
    v___x_8394_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_8394_, 0, v___x_8393_);
    lean_ctor_set(v___x_8394_, 1, v_msgData_8382_);
    v___x_8395_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8395_, 0, v___x_8394_);
    return v___x_8395_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8400_: *mut LeanObject = core::ptr::null_mut();
    v_res_8400_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_8396_, v___y_8397_, v___y_8398_);
    lean_dec(v___y_8398_);
    lean_dec_ref(v___y_8397_);
    return v_res_8400_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_8401_: *mut LeanObject,
    mut v___y_8402_: *mut LeanObject,
    mut v___y_8403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8410_: u8 = 0;
    let mut v___x_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_8405_ = lean_ctor_get(v___y_8402_, 5);
                v___x_8406_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_8401_, v___y_8402_, v___y_8403_);
                v_a_8407_ = lean_ctor_get(v___x_8406_, 0);
                v_isSharedCheck_8415_ = (!lean_is_exclusive(v___x_8406_)) as u8;
                if v_isSharedCheck_8415_ == 0 {
                    v___x_8409_ = v___x_8406_;
                    v_isShared_8410_ = v_isSharedCheck_8415_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_8407_);
                    lean_dec(v___x_8406_);
                    v___x_8409_ = lean_box(0);
                    v_isShared_8410_ = v_isSharedCheck_8415_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_8405_);
                v___x_8411_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8411_, 0, v_ref_8405_);
                lean_ctor_set(v___x_8411_, 1, v_a_8407_);
                if v_isShared_8410_ == 0 {
                    lean_ctor_set_tag(v___x_8409_, 1);
                    lean_ctor_set(v___x_8409_, 0, v___x_8411_);
                    v___x_8413_ = v___x_8409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8414_, 0, v___x_8411_);
                    v___x_8413_ = v_reuseFailAlloc_8414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_8416_: *mut LeanObject,
    mut v___y_8417_: *mut LeanObject,
    mut v___y_8418_: *mut LeanObject,
    mut v___y_8419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8420_: *mut LeanObject = core::ptr::null_mut();
    v_res_8420_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_8416_, v___y_8417_, v___y_8418_);
    lean_dec(v___y_8418_);
    lean_dec_ref(v___y_8417_);
    return v_res_8420_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    v___x_8422_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8423_ = l_Lean_stringToMessageData(v___x_8422_);
    return v___x_8423_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    v___x_8425_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8426_ = l_Lean_stringToMessageData(v___x_8425_);
    return v___x_8426_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(
    mut v___x_8427_: *mut LeanObject,
    mut v_decl_8428_: *mut LeanObject,
    mut v___y_8429_: *mut LeanObject,
    mut v___y_8430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: *mut LeanObject = core::ptr::null_mut();
    v___x_8432_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8433_ = l_Lean_MessageData_ofName(v___x_8427_);
    v___x_8434_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_8434_, 0, v___x_8432_);
    lean_ctor_set(v___x_8434_, 1, v___x_8433_);
    v___x_8435_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8436_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_8436_, 0, v___x_8434_);
    lean_ctor_set(v___x_8436_, 1, v___x_8435_);
    v___x_8437_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_8436_, v___y_8429_, v___y_8430_);
    return v___x_8437_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(
    mut v___x_8438_: *mut LeanObject,
    mut v_decl_8439_: *mut LeanObject,
    mut v___y_8440_: *mut LeanObject,
    mut v___y_8441_: *mut LeanObject,
    mut v___y_8442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8443_: *mut LeanObject = core::ptr::null_mut();
    v_res_8443_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_8438_, v_decl_8439_, v___y_8440_, v___y_8441_);
    lean_dec(v___y_8441_);
    lean_dec_ref(v___y_8440_);
    lean_dec(v_decl_8439_);
    return v_res_8443_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8496_: *mut LeanObject = core::ptr::null_mut();
    v___x_8494_ = lean_unsigned_to_nat(2729305610);
    v___x_8495_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8496_ = l_Lean_Name_num___override(v___x_8495_, v___x_8494_);
    return v___x_8496_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    v___x_8498_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8499_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8500_ = l_Lean_Name_str___override(v___x_8499_, v___x_8498_);
    return v___x_8500_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8504_: *mut LeanObject = core::ptr::null_mut();
    v___x_8502_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8503_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8504_ = l_Lean_Name_str___override(v___x_8503_, v___x_8502_);
    return v___x_8504_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8507_: *mut LeanObject = core::ptr::null_mut();
    v___x_8505_ = lean_unsigned_to_nat(2);
    v___x_8506_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8507_ = l_Lean_Name_num___override(v___x_8506_, v___x_8505_);
    return v___x_8507_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8514_: u8 = 0;
    let mut v___x_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8518_: *mut LeanObject = core::ptr::null_mut();
    v___x_8514_ = 0;
    v___x_8515_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8516_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8517_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8518_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_8518_, 0, v___x_8517_);
    lean_ctor_set(v___x_8518_, 1, v___x_8516_);
    lean_ctor_set(v___x_8518_, 2, v___x_8515_);
    lean_ctor_set_uint8(
        v___x_8518_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_8514_,
    );
    return v___x_8518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_8519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8522_: *mut LeanObject = core::ptr::null_mut();
    v___f_8519_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___f_8520_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8521_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8522_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_8522_, 0, v___x_8521_);
    lean_ctor_set(v___x_8522_, 1, v___f_8520_);
    lean_ctor_set(v___x_8522_, 2, v___f_8519_);
    return v___x_8522_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: *mut LeanObject = core::ptr::null_mut();
    v___x_8524_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8525_ = l_Lean_registerBuiltinAttribute(v___x_8524_);
    return v___x_8525_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(
    mut v_a_8526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8527_: *mut LeanObject = core::ptr::null_mut();
    v_res_8527_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
    return v_res_8527_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_8528_: *mut LeanObject,
    mut v_msg_8529_: *mut LeanObject,
    mut v___y_8530_: *mut LeanObject,
    mut v___y_8531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8533_: *mut LeanObject = core::ptr::null_mut();
    v___x_8533_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_8529_, v___y_8530_, v___y_8531_);
    return v___x_8533_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_8534_: *mut LeanObject,
    mut v_msg_8535_: *mut LeanObject,
    mut v___y_8536_: *mut LeanObject,
    mut v___y_8537_: *mut LeanObject,
    mut v___y_8538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8539_: *mut LeanObject = core::ptr::null_mut();
    v_res_8539_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_8534_, v_msg_8535_, v___y_8536_, v___y_8537_);
    lean_dec(v___y_8537_);
    lean_dec_ref(v___y_8536_);
    return v_res_8539_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8544_: *mut LeanObject = core::ptr::null_mut();
    v___x_8542_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8543_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
    v___x_8544_ = l_Lean_addBuiltinDocString(v___x_8542_, v___x_8543_);
    return v___x_8544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(
    mut v_a_8545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8546_: *mut LeanObject = core::ptr::null_mut();
    v_res_8546_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
    return v_res_8546_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(
    mut v___x_8547_: *mut LeanObject,
    mut v___x_8548_: *mut LeanObject,
    mut v_declName_8549_: *mut LeanObject,
    mut v_x_8550_: *mut LeanObject,
    mut v_attrKind_8551_: u8,
    mut v___y_8552_: *mut LeanObject,
    mut v___y_8553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8555_: u8 = 0;
    let mut v___x_8556_: u8 = 0;
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8562_: usize = 0;
    let mut v___x_8563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8577_: u8 = 0;
    let mut v___x_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8583_: u8 = 0;
    let mut v_unused_8584_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8555_ = 0;
                v___x_8556_ = 1;
                v___x_8557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8558_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8559_ = lean_unsigned_to_nat(32);
                v___x_8560_ = lean_mk_empty_array_with_capacity(v___x_8559_);
                v___x_8561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
                v___x_8562_ = 5usize;
                lean_inc_n(v___x_8547_, 6);
                v___x_8563_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_8563_, 0, v___x_8561_);
                lean_ctor_set(v___x_8563_, 1, v___x_8560_);
                lean_ctor_set(v___x_8563_, 2, v___x_8547_);
                lean_ctor_set(v___x_8563_, 3, v___x_8547_);
                lean_ctor_set_usize(v___x_8563_, 4, v___x_8562_);
                v___x_8564_ = lean_box(1);
                lean_inc_ref(v___x_8563_);
                v___x_8565_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_8565_, 0, v___x_8558_);
                lean_ctor_set(v___x_8565_, 1, v___x_8563_);
                lean_ctor_set(v___x_8565_, 2, v___x_8564_);
                v___x_8566_ = lean_mk_empty_array_with_capacity(v___x_8547_);
                v___x_8567_ = lean_box(0);
                lean_inc(v___x_8548_);
                v___x_8568_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_8568_, 0, v___x_8557_);
                lean_ctor_set(v___x_8568_, 1, v___x_8548_);
                lean_ctor_set(v___x_8568_, 2, v___x_8565_);
                lean_ctor_set(v___x_8568_, 3, v___x_8566_);
                lean_ctor_set(v___x_8568_, 4, v___x_8567_);
                lean_ctor_set(v___x_8568_, 5, v___x_8547_);
                lean_ctor_set(v___x_8568_, 6, v___x_8567_);
                lean_ctor_set_uint8(
                    v___x_8568_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_8555_,
                );
                lean_ctor_set_uint8(
                    v___x_8568_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_8555_,
                );
                lean_ctor_set_uint8(
                    v___x_8568_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_8555_,
                );
                lean_ctor_set_uint8(
                    v___x_8568_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_8556_,
                );
                v___x_8569_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_8569_, 0, v___x_8547_);
                lean_ctor_set(v___x_8569_, 1, v___x_8547_);
                lean_ctor_set(v___x_8569_, 2, v___x_8547_);
                lean_ctor_set(v___x_8569_, 3, v___x_8547_);
                lean_ctor_set(v___x_8569_, 4, v___x_8558_);
                lean_ctor_set(v___x_8569_, 5, v___x_8558_);
                lean_ctor_set(v___x_8569_, 6, v___x_8558_);
                lean_ctor_set(v___x_8569_, 7, v___x_8558_);
                lean_ctor_set(v___x_8569_, 8, v___x_8558_);
                lean_ctor_set(v___x_8569_, 9, v___x_8558_);
                v___x_8570_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8571_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
                v___x_8572_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_8572_, 0, v___x_8569_);
                lean_ctor_set(v___x_8572_, 1, v___x_8570_);
                lean_ctor_set(v___x_8572_, 2, v___x_8548_);
                lean_ctor_set(v___x_8572_, 3, v___x_8563_);
                lean_ctor_set(v___x_8572_, 4, v___x_8571_);
                v___x_8573_ = lean_st_mk_ref(v___x_8572_);
                v___x_8574_ = l_Lean_Meta_addCustomEliminator(
                    v_declName_8549_,
                    v_attrKind_8551_,
                    v___x_8555_,
                    v___x_8568_,
                    v___x_8573_,
                    v___y_8552_,
                    v___y_8553_,
                );
                lean_dec_ref_known(v___x_8568_, 7);
                if lean_obj_tag(v___x_8574_) == 0 {
                    v_isSharedCheck_8583_ = (!lean_is_exclusive(v___x_8574_)) as u8;
                    if v_isSharedCheck_8583_ == 0 {
                        v_unused_8584_ = lean_ctor_get(v___x_8574_, 0);
                        lean_dec(v_unused_8584_);
                        v___x_8576_ = v___x_8574_;
                        v_isShared_8577_ = v_isSharedCheck_8583_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_8574_);
                        v___x_8576_ = lean_box(0);
                        v_isShared_8577_ = v_isSharedCheck_8583_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_8573_);
                    return v___x_8574_;
                }
            }
            1 => {
                v___x_8578_ = lean_st_ref_get(v___x_8573_);
                lean_dec(v___x_8573_);
                lean_dec(v___x_8578_);
                v___x_8579_ = lean_box(0);
                if v_isShared_8577_ == 0 {
                    lean_ctor_set(v___x_8576_, 0, v___x_8579_);
                    v___x_8581_ = v___x_8576_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8582_, 0, v___x_8579_);
                    v___x_8581_ = v_reuseFailAlloc_8582_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(
    mut v___x_8585_: *mut LeanObject,
    mut v___x_8586_: *mut LeanObject,
    mut v_declName_8587_: *mut LeanObject,
    mut v_x_8588_: *mut LeanObject,
    mut v_attrKind_8589_: *mut LeanObject,
    mut v___y_8590_: *mut LeanObject,
    mut v___y_8591_: *mut LeanObject,
    mut v___y_8592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_8593_: u8 = 0;
    let mut v_res_8594_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_8593_ = (lean_unbox(v_attrKind_8589_) as u8);
    v_res_8594_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_8585_, v___x_8586_, v_declName_8587_, v_x_8588_, v_attrKind_boxed_8593_, v___y_8590_, v___y_8591_);
    lean_dec(v___y_8591_);
    lean_dec_ref(v___y_8590_);
    lean_dec(v_x_8588_);
    return v_res_8594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(
    mut v___x_8595_: *mut LeanObject,
    mut v_decl_8596_: *mut LeanObject,
    mut v___y_8597_: *mut LeanObject,
    mut v___y_8598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8605_: *mut LeanObject = core::ptr::null_mut();
    v___x_8600_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8601_ = l_Lean_MessageData_ofName(v___x_8595_);
    v___x_8602_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_8602_, 0, v___x_8600_);
    lean_ctor_set(v___x_8602_, 1, v___x_8601_);
    v___x_8603_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
    v___x_8604_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_8604_, 0, v___x_8602_);
    lean_ctor_set(v___x_8604_, 1, v___x_8603_);
    v___x_8605_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_8604_, v___y_8597_, v___y_8598_);
    return v___x_8605_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(
    mut v___x_8606_: *mut LeanObject,
    mut v_decl_8607_: *mut LeanObject,
    mut v___y_8608_: *mut LeanObject,
    mut v___y_8609_: *mut LeanObject,
    mut v___y_8610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8611_: *mut LeanObject = core::ptr::null_mut();
    v_res_8611_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_8606_, v_decl_8607_, v___y_8608_, v___y_8609_);
    lean_dec(v___y_8609_);
    lean_dec_ref(v___y_8608_);
    lean_dec(v_decl_8607_);
    return v_res_8611_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8644_: *mut LeanObject = core::ptr::null_mut();
    v___x_8643_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_;
    v___x_8644_ = l_Lean_registerBuiltinAttribute(v___x_8643_);
    return v___x_8644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(
    mut v_a_8645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8646_: *mut LeanObject = core::ptr::null_mut();
    v_res_8646_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
    return v_res_8646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: *mut LeanObject = core::ptr::null_mut();
    v___x_8649_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_;
    v___x_8650_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_;
    v___x_8651_ = l_Lean_addBuiltinDocString(v___x_8649_, v___x_8650_);
    return v___x_8651_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(
    mut v_a_8652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8653_: *mut LeanObject = core::ptr::null_mut();
    v_res_8653_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
    return v_res_8653_;
}
pub unsafe fn l_Lean_Meta_getCustomEliminators___redArg(
    mut v_a_8654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_8661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8664_: *mut LeanObject = core::ptr::null_mut();
    v___x_8656_ = lean_st_ref_get(v_a_8654_);
    v_env_8657_ = lean_ctor_get(v___x_8656_, 0);
    lean_inc_ref(v_env_8657_);
    lean_dec(v___x_8656_);
    v___x_8658_ = l_Lean_Meta_customEliminatorExt;
    v_ext_8659_ = lean_ctor_get(v___x_8658_, 1);
    v_toEnvExtension_8660_ = lean_ctor_get(v_ext_8659_, 0);
    v_asyncMode_8661_ = lean_ctor_get(v_toEnvExtension_8660_, 2);
    v___x_8662_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
    v___x_8663_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_8662_,
        v___x_8658_,
        v_env_8657_,
        v_asyncMode_8661_,
    );
    v___x_8664_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8664_, 0, v___x_8663_);
    return v___x_8664_;
}
pub unsafe fn l_Lean_Meta_getCustomEliminators___redArg___boxed(
    mut v_a_8665_: *mut LeanObject,
    mut v_a_8666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8667_: *mut LeanObject = core::ptr::null_mut();
    v_res_8667_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_8665_);
    lean_dec(v_a_8665_);
    return v_res_8667_;
}
pub unsafe fn l_Lean_Meta_getCustomEliminators(
    mut v_a_8668_: *mut LeanObject,
    mut v_a_8669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8671_: *mut LeanObject = core::ptr::null_mut();
    v___x_8671_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_8669_);
    return v___x_8671_;
}
pub unsafe fn l_Lean_Meta_getCustomEliminators___boxed(
    mut v_a_8672_: *mut LeanObject,
    mut v_a_8673_: *mut LeanObject,
    mut v_a_8674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8675_: *mut LeanObject = core::ptr::null_mut();
    v_res_8675_ = l_Lean_Meta_getCustomEliminators(v_a_8672_, v_a_8673_);
    lean_dec(v_a_8673_);
    lean_dec_ref(v_a_8672_);
    return v_res_8675_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_a_8676_: *mut LeanObject,
    mut v_x_8677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_8679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8689_: u8 = 0;
    let mut v___x_8691_: u8 = 0;
    let mut v___x_8693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8694_: u8 = 0;
    let mut v___x_8695_: u8 = 0;
    let mut v___x_8697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8677_) == 0 {
                    v___x_8678_ = lean_box(0);
                    return v___x_8678_;
                } else {
                    v_key_8679_ = lean_ctor_get(v_x_8677_, 0);
                    v_value_8680_ = lean_ctor_get(v_x_8677_, 1);
                    v_tail_8681_ = lean_ctor_get(v_x_8677_, 2);
                    v_fst_8682_ = lean_ctor_get(v_key_8679_, 0);
                    v_snd_8683_ = lean_ctor_get(v_key_8679_, 1);
                    v_fst_8684_ = lean_ctor_get(v_a_8676_, 0);
                    v_snd_8685_ = lean_ctor_get(v_a_8676_, 1);
                    v___x_8694_ = (lean_unbox(v_fst_8682_) as u8);
                    if v___x_8694_ == 0 {
                        v___x_8695_ = (lean_unbox(v_fst_8684_) as u8);
                        if v___x_8695_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_8677_ = v_tail_8681_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_8697_ = (lean_unbox(v_fst_8684_) as u8);
                        if v___x_8697_ == 0 {
                            v_x_8677_ = v_tail_8681_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8687_ = lean_array_get_size(v_snd_8683_);
                v___x_8688_ = lean_array_get_size(v_snd_8685_);
                v___x_8689_ = lean_nat_dec_eq(v___x_8687_, v___x_8688_);
                if v___x_8689_ == 0 {
                    v_x_8677_ = v_tail_8681_;
                    state = 0;
                    continue;
                } else {
                    v___x_8691_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_8683_, v_snd_8685_, v___x_8687_);
                    if v___x_8691_ == 0 {
                        v_x_8677_ = v_tail_8681_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_8680_);
                        v___x_8693_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_8693_, 0, v_value_8680_);
                        return v___x_8693_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_a_8699_: *mut LeanObject,
    mut v_x_8700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8701_: *mut LeanObject = core::ptr::null_mut();
    v_res_8701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_8699_, v_x_8700_);
    lean_dec(v_x_8700_);
    lean_dec_ref(v_a_8699_);
    return v_res_8701_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(
    mut v_m_8702_: *mut LeanObject,
    mut v_a_8703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8709_: u64 = 0;
    let mut v___y_8710_: u64 = 0;
    let mut v___x_8711_: u64 = 0;
    let mut v___x_8712_: u64 = 0;
    let mut v___x_8713_: u64 = 0;
    let mut v_fold_8714_: u64 = 0;
    let mut v___x_8715_: u64 = 0;
    let mut v___x_8716_: u64 = 0;
    let mut v___x_8717_: u64 = 0;
    let mut v___x_8718_: usize = 0;
    let mut v___x_8719_: usize = 0;
    let mut v___x_8720_: usize = 0;
    let mut v___x_8721_: usize = 0;
    let mut v___x_8722_: usize = 0;
    let mut v___x_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8726_: u64 = 0;
    let mut v___x_8727_: u64 = 0;
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8730_: u8 = 0;
    let mut v___x_8731_: u8 = 0;
    let mut v___x_8732_: usize = 0;
    let mut v___x_8733_: usize = 0;
    let mut v___x_8734_: u64 = 0;
    let mut v___x_8735_: usize = 0;
    let mut v___x_8736_: usize = 0;
    let mut v___x_8737_: u64 = 0;
    let mut v___x_8738_: u8 = 0;
    let mut v___x_8739_: u64 = 0;
    let mut v___x_8740_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_8704_ = lean_ctor_get(v_m_8702_, 1);
                v_fst_8705_ = lean_ctor_get(v_a_8703_, 0);
                v_snd_8706_ = lean_ctor_get(v_a_8703_, 1);
                v___x_8707_ = lean_array_get_size(v_buckets_8704_);
                v___x_8738_ = (lean_unbox(v_fst_8705_) as u8);
                if v___x_8738_ == 0 {
                    v___x_8739_ = 13u64;
                    v___y_8726_ = v___x_8739_;
                    state = 2;
                    continue;
                } else {
                    v___x_8740_ = 11u64;
                    v___y_8726_ = v___x_8740_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8711_ = lean_uint64_mix_hash(v___y_8709_, v___y_8710_);
                v___x_8712_ = 32u64;
                v___x_8713_ = lean_uint64_shift_right(v___x_8711_, v___x_8712_);
                v_fold_8714_ = lean_uint64_xor(v___x_8711_, v___x_8713_);
                v___x_8715_ = 16u64;
                v___x_8716_ = lean_uint64_shift_right(v_fold_8714_, v___x_8715_);
                v___x_8717_ = lean_uint64_xor(v_fold_8714_, v___x_8716_);
                v___x_8718_ = lean_uint64_to_usize(v___x_8717_);
                v___x_8719_ = lean_usize_of_nat(v___x_8707_);
                v___x_8720_ = 1usize;
                v___x_8721_ = lean_usize_sub(v___x_8719_, v___x_8720_);
                v___x_8722_ = lean_usize_land(v___x_8718_, v___x_8721_);
                v___x_8723_ = lean_array_uget_borrowed(v_buckets_8704_, v___x_8722_);
                v___x_8724_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_8703_, v___x_8723_);
                return v___x_8724_;
            }
            2 => {
                v___x_8727_ = 7u64;
                v___x_8728_ = lean_unsigned_to_nat(0);
                v___x_8729_ = lean_array_get_size(v_snd_8706_);
                v___x_8730_ = lean_nat_dec_lt(v___x_8728_, v___x_8729_);
                if v___x_8730_ == 0 {
                    v___y_8709_ = v___y_8726_;
                    v___y_8710_ = v___x_8727_;
                    state = 1;
                    continue;
                } else {
                    v___x_8731_ = lean_nat_dec_le(v___x_8729_, v___x_8729_);
                    if v___x_8731_ == 0 {
                        if v___x_8730_ == 0 {
                            v___y_8709_ = v___y_8726_;
                            v___y_8710_ = v___x_8727_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8732_ = 0usize;
                            v___x_8733_ = lean_usize_of_nat(v___x_8729_);
                            v___x_8734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_8706_, v___x_8732_, v___x_8733_, v___x_8727_);
                            v___y_8709_ = v___y_8726_;
                            v___y_8710_ = v___x_8734_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_8735_ = 0usize;
                        v___x_8736_ = lean_usize_of_nat(v___x_8729_);
                        v___x_8737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_8706_, v___x_8735_, v___x_8736_, v___x_8727_);
                        v___y_8709_ = v___y_8726_;
                        v___y_8710_ = v___x_8737_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(
    mut v_m_8741_: *mut LeanObject,
    mut v_a_8742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8743_: *mut LeanObject = core::ptr::null_mut();
    v_res_8743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_8741_, v_a_8742_);
    lean_dec_ref(v_a_8742_);
    lean_dec_ref(v_m_8741_);
    return v_res_8743_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_keys_8744_: *mut LeanObject,
    mut v_vals_8745_: *mut LeanObject,
    mut v_i_8746_: *mut LeanObject,
    mut v_k_8747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: u8 = 0;
    let mut v___x_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8761_: u8 = 0;
    let mut v___x_8762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: u8 = 0;
    let mut v___x_8765_: u8 = 0;
    let mut v___x_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: u8 = 0;
    let mut v___x_8769_: u8 = 0;
    let mut v___x_8770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8752_ = lean_array_get_size(v_keys_8744_);
                v___x_8753_ = lean_nat_dec_lt(v_i_8746_, v___x_8752_);
                if v___x_8753_ == 0 {
                    lean_dec(v_i_8746_);
                    v___x_8754_ = lean_box(0);
                    return v___x_8754_;
                } else {
                    v_fst_8755_ = lean_ctor_get(v_k_8747_, 0);
                    v_snd_8756_ = lean_ctor_get(v_k_8747_, 1);
                    v_k_x27_8757_ = lean_array_fget_borrowed(v_keys_8744_, v_i_8746_);
                    v_fst_8758_ = lean_ctor_get(v_k_x27_8757_, 0);
                    v_snd_8759_ = lean_ctor_get(v_k_x27_8757_, 1);
                    v___x_8768_ = (lean_unbox(v_fst_8755_) as u8);
                    if v___x_8768_ == 0 {
                        v___x_8769_ = (lean_unbox(v_fst_8758_) as u8);
                        if v___x_8769_ == 0 {
                            v___y_8761_ = v___x_8753_;
                            state = 2;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_8770_ = (lean_unbox(v_fst_8758_) as u8);
                        v___y_8761_ = v___x_8770_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8749_ = lean_unsigned_to_nat(1);
                v___x_8750_ = lean_nat_add(v_i_8746_, v___x_8749_);
                lean_dec(v_i_8746_);
                v_i_8746_ = v___x_8750_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_8761_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_8762_ = lean_array_get_size(v_snd_8756_);
                    v___x_8763_ = lean_array_get_size(v_snd_8759_);
                    v___x_8764_ = lean_nat_dec_eq(v___x_8762_, v___x_8763_);
                    if v___x_8764_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_8765_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_8756_, v_snd_8759_, v___x_8762_);
                        if v___x_8765_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_8766_ = lean_array_fget_borrowed(v_vals_8745_, v_i_8746_);
                            lean_dec(v_i_8746_);
                            lean_inc(v___x_8766_);
                            v___x_8767_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8767_, 0, v___x_8766_);
                            return v___x_8767_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_8771_: *mut LeanObject,
    mut v_vals_8772_: *mut LeanObject,
    mut v_i_8773_: *mut LeanObject,
    mut v_k_8774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8775_: *mut LeanObject = core::ptr::null_mut();
    v_res_8775_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_8771_, v_vals_8772_, v_i_8773_, v_k_8774_);
    lean_dec_ref(v_k_8774_);
    lean_dec_ref(v_vals_8772_);
    lean_dec_ref(v_keys_8771_);
    return v_res_8775_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(
    mut v_x_8776_: *mut LeanObject,
    mut v_x_8777_: usize,
    mut v_x_8778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: usize = 0;
    let mut v___x_8782_: usize = 0;
    let mut v___x_8783_: usize = 0;
    let mut v_j_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_8786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8795_: u8 = 0;
    let mut v___x_8796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8797_: u8 = 0;
    let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8800_: u8 = 0;
    let mut v___x_8801_: u8 = 0;
    let mut v___x_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: u8 = 0;
    let mut v___x_8804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_8805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8806_: usize = 0;
    let mut v___x_8808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_8809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_8810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8776_) == 0 {
                    v_es_8779_ = lean_ctor_get(v_x_8776_, 0);
                    v___x_8780_ = lean_box(2);
                    v___x_8781_ = 5usize;
                    v___x_8782_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_8783_ = lean_usize_land(v_x_8777_, v___x_8782_);
                    v_j_8784_ = lean_usize_to_nat(v___x_8783_);
                    v___x_8785_ = lean_array_get_borrowed(v___x_8780_, v_es_8779_, v_j_8784_);
                    lean_dec(v_j_8784_);
                    match lean_obj_tag(v___x_8785_) {
                        0 => {
                            v_key_8786_ = lean_ctor_get(v___x_8785_, 0);
                            v_val_8787_ = lean_ctor_get(v___x_8785_, 1);
                            v_fst_8788_ = lean_ctor_get(v_x_8778_, 0);
                            v_snd_8789_ = lean_ctor_get(v_x_8778_, 1);
                            v_fst_8790_ = lean_ctor_get(v_key_8786_, 0);
                            v_snd_8791_ = lean_ctor_get(v_key_8786_, 1);
                            v___x_8800_ = (lean_unbox(v_fst_8788_) as u8);
                            if v___x_8800_ == 0 {
                                v___x_8801_ = (lean_unbox(v_fst_8790_) as u8);
                                if v___x_8801_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_8802_ = lean_box(0);
                                    return v___x_8802_;
                                }
                            } else {
                                v___x_8803_ = (lean_unbox(v_fst_8790_) as u8);
                                if v___x_8803_ == 0 {
                                    v___x_8804_ = lean_box(0);
                                    return v___x_8804_;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_node_8805_ = lean_ctor_get(v___x_8785_, 0);
                            v___x_8806_ = lean_usize_shift_right(v_x_8777_, v___x_8781_);
                            v_x_8776_ = v_node_8805_;
                            v_x_8777_ = v___x_8806_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_8808_ = lean_box(0);
                            return v___x_8808_;
                        }
                    }
                } else {
                    v_ks_8809_ = lean_ctor_get(v_x_8776_, 0);
                    v_vs_8810_ = lean_ctor_get(v_x_8776_, 1);
                    v___x_8811_ = lean_unsigned_to_nat(0);
                    v___x_8812_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_8809_, v_vs_8810_, v___x_8811_, v_x_8778_);
                    return v___x_8812_;
                }
            }
            1 => {
                v___x_8793_ = lean_array_get_size(v_snd_8789_);
                v___x_8794_ = lean_array_get_size(v_snd_8791_);
                v___x_8795_ = lean_nat_dec_eq(v___x_8793_, v___x_8794_);
                if v___x_8795_ == 0 {
                    v___x_8796_ = lean_box(0);
                    return v___x_8796_;
                } else {
                    v___x_8797_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_8789_, v_snd_8791_, v___x_8793_);
                    if v___x_8797_ == 0 {
                        v___x_8798_ = lean_box(0);
                        return v___x_8798_;
                    } else {
                        lean_inc(v_val_8787_);
                        v___x_8799_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_8799_, 0, v_val_8787_);
                        return v___x_8799_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_8813_: *mut LeanObject,
    mut v_x_8814_: *mut LeanObject,
    mut v_x_8815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2279__boxed_8816_: usize = 0;
    let mut v_res_8817_: *mut LeanObject = core::ptr::null_mut();
    v_x_2279__boxed_8816_ = lean_unbox_usize(v_x_8814_);
    lean_dec(v_x_8814_);
    v_res_8817_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_8813_, v_x_2279__boxed_8816_, v_x_8815_);
    lean_dec_ref(v_x_8815_);
    lean_dec_ref(v_x_8813_);
    return v_res_8817_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(
    mut v_x_8818_: *mut LeanObject,
    mut v_x_8819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8821_: u64 = 0;
    let mut v___y_8822_: u64 = 0;
    let mut v___x_8823_: u64 = 0;
    let mut v___x_8824_: usize = 0;
    let mut v___x_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8829_: u64 = 0;
    let mut v___x_8830_: u64 = 0;
    let mut v___x_8831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: u8 = 0;
    let mut v___x_8834_: u8 = 0;
    let mut v___x_8835_: usize = 0;
    let mut v___x_8836_: usize = 0;
    let mut v___x_8837_: u64 = 0;
    let mut v___x_8838_: usize = 0;
    let mut v___x_8839_: usize = 0;
    let mut v___x_8840_: u64 = 0;
    let mut v___x_8841_: u8 = 0;
    let mut v___x_8842_: u64 = 0;
    let mut v___x_8843_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_8826_ = lean_ctor_get(v_x_8819_, 0);
                v_snd_8827_ = lean_ctor_get(v_x_8819_, 1);
                v___x_8841_ = (lean_unbox(v_fst_8826_) as u8);
                if v___x_8841_ == 0 {
                    v___x_8842_ = 13u64;
                    v___y_8829_ = v___x_8842_;
                    state = 2;
                    continue;
                } else {
                    v___x_8843_ = 11u64;
                    v___y_8829_ = v___x_8843_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8823_ = lean_uint64_mix_hash(v___y_8821_, v___y_8822_);
                v___x_8824_ = lean_uint64_to_usize(v___x_8823_);
                v___x_8825_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_8818_, v___x_8824_, v_x_8819_);
                return v___x_8825_;
            }
            2 => {
                v___x_8830_ = 7u64;
                v___x_8831_ = lean_unsigned_to_nat(0);
                v___x_8832_ = lean_array_get_size(v_snd_8827_);
                v___x_8833_ = lean_nat_dec_lt(v___x_8831_, v___x_8832_);
                if v___x_8833_ == 0 {
                    v___y_8821_ = v___y_8829_;
                    v___y_8822_ = v___x_8830_;
                    state = 1;
                    continue;
                } else {
                    v___x_8834_ = lean_nat_dec_le(v___x_8832_, v___x_8832_);
                    if v___x_8834_ == 0 {
                        if v___x_8833_ == 0 {
                            v___y_8821_ = v___y_8829_;
                            v___y_8822_ = v___x_8830_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8835_ = 0usize;
                            v___x_8836_ = lean_usize_of_nat(v___x_8832_);
                            v___x_8837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_8827_, v___x_8835_, v___x_8836_, v___x_8830_);
                            v___y_8821_ = v___y_8829_;
                            v___y_8822_ = v___x_8837_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_8838_ = 0usize;
                        v___x_8839_ = lean_usize_of_nat(v___x_8832_);
                        v___x_8840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_8827_, v___x_8838_, v___x_8839_, v___x_8830_);
                        v___y_8821_ = v___y_8829_;
                        v___y_8822_ = v___x_8840_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_8844_: *mut LeanObject,
    mut v_x_8845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8846_: *mut LeanObject = core::ptr::null_mut();
    v_res_8846_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_8844_, v_x_8845_);
    lean_dec_ref(v_x_8845_);
    lean_dec_ref(v_x_8844_);
    return v_res_8846_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(
    mut v_x_8847_: *mut LeanObject,
    mut v_x_8848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_8849_: u8 = 0;
    v_stage_u2081_8849_ = lean_ctor_get_uint8(
        v_x_8847_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_8849_ == 0 {
        let mut v_map_u2081_8850_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_8851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8852_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_8850_ = lean_ctor_get(v_x_8847_, 0);
        v_map_u2082_8851_ = lean_ctor_get(v_x_8847_, 1);
        v___x_8852_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_8851_, v_x_8848_);
        if lean_obj_tag(v___x_8852_) == 0 {
            let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
            v___x_8853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_8850_, v_x_8848_);
            return v___x_8853_;
        } else {
            return v___x_8852_;
        }
    } else {
        let mut v_map_u2081_8854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8855_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_8854_ = lean_ctor_get(v_x_8847_, 0);
        v___x_8855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_8854_, v_x_8848_);
        return v___x_8855_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(
    mut v_x_8856_: *mut LeanObject,
    mut v_x_8857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8858_: *mut LeanObject = core::ptr::null_mut();
    v_res_8858_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(
        v_x_8856_, v_x_8857_,
    );
    lean_dec_ref(v_x_8857_);
    lean_dec_ref(v_x_8856_);
    return v_res_8858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(
    mut v_as_8861_: *mut LeanObject,
    mut v_sz_8862_: usize,
    mut v_i_8863_: usize,
    mut v_b_8864_: *mut LeanObject,
    mut v___y_8865_: *mut LeanObject,
    mut v___y_8866_: *mut LeanObject,
    mut v___y_8867_: *mut LeanObject,
    mut v___y_8868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8870_: u8 = 0;
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8879_: u8 = 0;
    let mut v_snd_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8883_: u8 = 0;
    let mut v___x_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8891_: usize = 0;
    let mut v___x_8892_: usize = 0;
    let mut v_reuseFailAlloc_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8902_: u8 = 0;
    let mut v_unused_8903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8904_: u8 = 0;
    let mut v_a_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8908_: u8 = 0;
    let mut v___x_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8912_: u8 = 0;
    let mut v_a_8913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8916_: u8 = 0;
    let mut v___x_8918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8870_ = lean_usize_dec_lt(v_i_8863_, v_sz_8862_);
                if v___x_8870_ == 0 {
                    v___x_8871_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8871_, 0, v_b_8864_);
                    return v___x_8871_;
                } else {
                    v_a_8872_ = lean_array_uget_borrowed(v_as_8861_, v_i_8863_);
                    lean_inc(v___y_8868_);
                    lean_inc_ref(v___y_8867_);
                    lean_inc(v___y_8866_);
                    lean_inc_ref(v___y_8865_);
                    lean_inc(v_a_8872_);
                    v___x_8873_ = lean_infer_type(
                        v_a_8872_,
                        v___y_8865_,
                        v___y_8866_,
                        v___y_8867_,
                        v___y_8868_,
                    );
                    if lean_obj_tag(v___x_8873_) == 0 {
                        v_a_8874_ = lean_ctor_get(v___x_8873_, 0);
                        lean_inc(v_a_8874_);
                        lean_dec_ref_known(v___x_8873_, 1);
                        v___x_8875_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_8874_, v___y_8866_);
                        if lean_obj_tag(v___x_8875_) == 0 {
                            v_a_8876_ = lean_ctor_get(v___x_8875_, 0);
                            v_isSharedCheck_8904_ = (!lean_is_exclusive(v___x_8875_)) as u8;
                            if v_isSharedCheck_8904_ == 0 {
                                v___x_8878_ = v___x_8875_;
                                v_isShared_8879_ = v_isSharedCheck_8904_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_8876_);
                                lean_dec(v___x_8875_);
                                v___x_8878_ = lean_box(0);
                                v_isShared_8879_ = v_isSharedCheck_8904_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_8864_);
                            v_a_8905_ = lean_ctor_get(v___x_8875_, 0);
                            v_isSharedCheck_8912_ = (!lean_is_exclusive(v___x_8875_)) as u8;
                            if v_isSharedCheck_8912_ == 0 {
                                v___x_8907_ = v___x_8875_;
                                v_isShared_8908_ = v_isSharedCheck_8912_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_8905_);
                                lean_dec(v___x_8875_);
                                v___x_8907_ = lean_box(0);
                                v_isShared_8908_ = v_isSharedCheck_8912_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_8864_);
                        v_a_8913_ = lean_ctor_get(v___x_8873_, 0);
                        v_isSharedCheck_8920_ = (!lean_is_exclusive(v___x_8873_)) as u8;
                        if v_isSharedCheck_8920_ == 0 {
                            v___x_8915_ = v___x_8873_;
                            v_isShared_8916_ = v_isSharedCheck_8920_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_8913_);
                            lean_dec(v___x_8873_);
                            v___x_8915_ = lean_box(0);
                            v_isShared_8916_ = v_isSharedCheck_8920_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_8880_ = lean_ctor_get(v_b_8864_, 1);
                v_isSharedCheck_8902_ = (!lean_is_exclusive(v_b_8864_)) as u8;
                if v_isSharedCheck_8902_ == 0 {
                    v_unused_8903_ = lean_ctor_get(v_b_8864_, 0);
                    lean_dec(v_unused_8903_);
                    v___x_8882_ = v_b_8864_;
                    v_isShared_8883_ = v_isSharedCheck_8902_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_8880_);
                    lean_dec(v_b_8864_);
                    v___x_8882_ = lean_box(0);
                    v_isShared_8883_ = v_isSharedCheck_8902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8884_ = l_Lean_Expr_headBeta(v_a_8876_);
                v___x_8885_ = l_Lean_Expr_getAppFn(v___x_8884_);
                lean_dec_ref(v___x_8884_);
                if lean_obj_tag(v___x_8885_) == 4 {
                    lean_del_object(v___x_8878_);
                    v_declName_8886_ = lean_ctor_get(v___x_8885_, 0);
                    lean_inc(v_declName_8886_);
                    lean_dec_ref_known(v___x_8885_, 2);
                    v___x_8887_ = lean_box(0);
                    v___x_8888_ = lean_array_push(v_snd_8880_, v_declName_8886_);
                    if v_isShared_8883_ == 0 {
                        lean_ctor_set(v___x_8882_, 1, v___x_8888_);
                        lean_ctor_set(v___x_8882_, 0, v___x_8887_);
                        v___x_8890_ = v___x_8882_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8894_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8894_, 0, v___x_8887_);
                        lean_ctor_set(v_reuseFailAlloc_8894_, 1, v___x_8888_);
                        v___x_8890_ = v_reuseFailAlloc_8894_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_8885_);
                    v___x_8895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0;
                    if v_isShared_8883_ == 0 {
                        lean_ctor_set(v___x_8882_, 0, v___x_8895_);
                        v___x_8897_ = v___x_8882_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8901_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8901_, 0, v___x_8895_);
                        lean_ctor_set(v_reuseFailAlloc_8901_, 1, v_snd_8880_);
                        v___x_8897_ = v_reuseFailAlloc_8901_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_8891_ = 1usize;
                v___x_8892_ = lean_usize_add(v_i_8863_, v___x_8891_);
                v_i_8863_ = v___x_8892_;
                v_b_8864_ = v___x_8890_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_8879_ == 0 {
                    lean_ctor_set(v___x_8878_, 0, v___x_8897_);
                    v___x_8899_ = v___x_8878_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8900_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8900_, 0, v___x_8897_);
                    v___x_8899_ = v_reuseFailAlloc_8900_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8899_;
            }
            6 => {
                if v_isShared_8908_ == 0 {
                    v___x_8910_ = v___x_8907_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8911_, 0, v_a_8905_);
                    v___x_8910_ = v_reuseFailAlloc_8911_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8910_;
            }
            8 => {
                if v_isShared_8916_ == 0 {
                    v___x_8918_ = v___x_8915_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8919_, 0, v_a_8913_);
                    v___x_8918_ = v_reuseFailAlloc_8919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(
    mut v_as_8921_: *mut LeanObject,
    mut v_sz_8922_: *mut LeanObject,
    mut v_i_8923_: *mut LeanObject,
    mut v_b_8924_: *mut LeanObject,
    mut v___y_8925_: *mut LeanObject,
    mut v___y_8926_: *mut LeanObject,
    mut v___y_8927_: *mut LeanObject,
    mut v___y_8928_: *mut LeanObject,
    mut v___y_8929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8930_: usize = 0;
    let mut v_i_boxed_8931_: usize = 0;
    let mut v_res_8932_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8930_ = lean_unbox_usize(v_sz_8922_);
    lean_dec(v_sz_8922_);
    v_i_boxed_8931_ = lean_unbox_usize(v_i_8923_);
    lean_dec(v_i_8923_);
    v_res_8932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_8921_, v_sz_boxed_8930_, v_i_boxed_8931_, v_b_8924_, v___y_8925_, v___y_8926_, v___y_8927_, v___y_8928_);
    lean_dec(v___y_8928_);
    lean_dec_ref(v___y_8927_);
    lean_dec(v___y_8926_);
    lean_dec_ref(v___y_8925_);
    lean_dec_ref(v_as_8921_);
    return v_res_8932_;
}
pub unsafe fn l_Lean_Meta_getCustomEliminator_x3f(
    mut v_targets_8936_: *mut LeanObject,
    mut v_induction_8937_: u8,
    mut v_a_8938_: *mut LeanObject,
    mut v_a_8939_: *mut LeanObject,
    mut v_a_8940_: *mut LeanObject,
    mut v_a_8941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8944_: usize = 0;
    let mut v___x_8945_: usize = 0;
    let mut v___x_8946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8950_: u8 = 0;
    let mut v_fst_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8955_: u8 = 0;
    let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_8961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8972_: u8 = 0;
    let mut v_unused_8973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8978_: u8 = 0;
    let mut v_a_8979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8982_: u8 = 0;
    let mut v___x_8984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8943_ = l_Lean_Meta_getCustomEliminator_x3f___closed__0;
                v_sz_8944_ = lean_array_size(v_targets_8936_);
                v___x_8945_ = 0usize;
                v___x_8946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_8936_, v_sz_8944_, v___x_8945_, v___x_8943_, v_a_8938_, v_a_8939_, v_a_8940_, v_a_8941_);
                if lean_obj_tag(v___x_8946_) == 0 {
                    v_a_8947_ = lean_ctor_get(v___x_8946_, 0);
                    v_isSharedCheck_8978_ = (!lean_is_exclusive(v___x_8946_)) as u8;
                    if v_isSharedCheck_8978_ == 0 {
                        v___x_8949_ = v___x_8946_;
                        v_isShared_8950_ = v_isSharedCheck_8978_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8947_);
                        lean_dec(v___x_8946_);
                        v___x_8949_ = lean_box(0);
                        v_isShared_8950_ = v_isSharedCheck_8978_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8979_ = lean_ctor_get(v___x_8946_, 0);
                    v_isSharedCheck_8986_ = (!lean_is_exclusive(v___x_8946_)) as u8;
                    if v_isSharedCheck_8986_ == 0 {
                        v___x_8981_ = v___x_8946_;
                        v_isShared_8982_ = v_isSharedCheck_8986_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8979_);
                        lean_dec(v___x_8946_);
                        v___x_8981_ = lean_box(0);
                        v_isShared_8982_ = v_isSharedCheck_8986_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8951_ = lean_ctor_get(v_a_8947_, 0);
                if lean_obj_tag(v_fst_8951_) == 0 {
                    v_snd_8952_ = lean_ctor_get(v_a_8947_, 1);
                    v_isSharedCheck_8972_ = (!lean_is_exclusive(v_a_8947_)) as u8;
                    if v_isSharedCheck_8972_ == 0 {
                        v_unused_8973_ = lean_ctor_get(v_a_8947_, 0);
                        lean_dec(v_unused_8973_);
                        v___x_8954_ = v_a_8947_;
                        v_isShared_8955_ = v_isSharedCheck_8972_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_8952_);
                        lean_dec(v_a_8947_);
                        v___x_8954_ = lean_box(0);
                        v_isShared_8955_ = v_isSharedCheck_8972_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_8951_);
                    lean_dec(v_a_8947_);
                    v_val_8974_ = lean_ctor_get(v_fst_8951_, 0);
                    lean_inc(v_val_8974_);
                    lean_dec_ref_known(v_fst_8951_, 1);
                    if v_isShared_8950_ == 0 {
                        lean_ctor_set(v___x_8949_, 0, v_val_8974_);
                        v___x_8976_ = v___x_8949_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8977_, 0, v_val_8974_);
                        v___x_8976_ = v_reuseFailAlloc_8977_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8956_ = lean_st_ref_get(v_a_8941_);
                v_env_8957_ = lean_ctor_get(v___x_8956_, 0);
                lean_inc_ref(v_env_8957_);
                lean_dec(v___x_8956_);
                v___x_8958_ = l_Lean_Meta_customEliminatorExt;
                v_ext_8959_ = lean_ctor_get(v___x_8958_, 1);
                v_toEnvExtension_8960_ = lean_ctor_get(v_ext_8959_, 0);
                v_asyncMode_8961_ = lean_ctor_get(v_toEnvExtension_8960_, 2);
                v___x_8962_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
                v___x_8963_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_8962_,
                    v___x_8958_,
                    v_env_8957_,
                    v_asyncMode_8961_,
                );
                v___x_8964_ = lean_box((v_induction_8937_) as usize);
                if v_isShared_8955_ == 0 {
                    lean_ctor_set(v___x_8954_, 0, v___x_8964_);
                    v___x_8966_ = v___x_8954_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8971_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8971_, 0, v___x_8964_);
                    lean_ctor_set(v_reuseFailAlloc_8971_, 1, v_snd_8952_);
                    v___x_8966_ = v_reuseFailAlloc_8971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8967_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_8963_, v___x_8966_);
                lean_dec_ref(v___x_8966_);
                lean_dec(v___x_8963_);
                if v_isShared_8950_ == 0 {
                    lean_ctor_set(v___x_8949_, 0, v___x_8967_);
                    v___x_8969_ = v___x_8949_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8970_, 0, v___x_8967_);
                    v___x_8969_ = v_reuseFailAlloc_8970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8969_;
            }
            5 => {
                return v___x_8976_;
            }
            6 => {
                if v_isShared_8982_ == 0 {
                    v___x_8984_ = v___x_8981_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8985_, 0, v_a_8979_);
                    v___x_8984_ = v_reuseFailAlloc_8985_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getCustomEliminator_x3f___boxed(
    mut v_targets_8987_: *mut LeanObject,
    mut v_induction_8988_: *mut LeanObject,
    mut v_a_8989_: *mut LeanObject,
    mut v_a_8990_: *mut LeanObject,
    mut v_a_8991_: *mut LeanObject,
    mut v_a_8992_: *mut LeanObject,
    mut v_a_8993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_induction_boxed_8994_: u8 = 0;
    let mut v_res_8995_: *mut LeanObject = core::ptr::null_mut();
    v_induction_boxed_8994_ = (lean_unbox(v_induction_8988_) as u8);
    v_res_8995_ = l_Lean_Meta_getCustomEliminator_x3f(
        v_targets_8987_,
        v_induction_boxed_8994_,
        v_a_8989_,
        v_a_8990_,
        v_a_8991_,
        v_a_8992_,
    );
    lean_dec(v_a_8992_);
    lean_dec_ref(v_a_8991_);
    lean_dec(v_a_8990_);
    lean_dec_ref(v_a_8989_);
    lean_dec_ref(v_targets_8987_);
    return v_res_8995_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(
    mut v_00_u03b2_8996_: *mut LeanObject,
    mut v_x_8997_: *mut LeanObject,
    mut v_x_8998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8999_: *mut LeanObject = core::ptr::null_mut();
    v___x_8999_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(
        v_x_8997_, v_x_8998_,
    );
    return v___x_8999_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(
    mut v_00_u03b2_9000_: *mut LeanObject,
    mut v_x_9001_: *mut LeanObject,
    mut v_x_9002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9003_: *mut LeanObject = core::ptr::null_mut();
    v_res_9003_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(
        v_00_u03b2_9000_,
        v_x_9001_,
        v_x_9002_,
    );
    lean_dec_ref(v_x_9002_);
    lean_dec_ref(v_x_9001_);
    return v_res_9003_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(
    mut v_00_u03b2_9004_: *mut LeanObject,
    mut v_x_9005_: *mut LeanObject,
    mut v_x_9006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9007_: *mut LeanObject = core::ptr::null_mut();
    v___x_9007_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_9005_, v_x_9006_);
    return v___x_9007_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_9008_: *mut LeanObject,
    mut v_x_9009_: *mut LeanObject,
    mut v_x_9010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9011_: *mut LeanObject = core::ptr::null_mut();
    v_res_9011_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_9008_, v_x_9009_, v_x_9010_);
    lean_dec_ref(v_x_9010_);
    lean_dec_ref(v_x_9009_);
    return v_res_9011_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(
    mut v_00_u03b2_9012_: *mut LeanObject,
    mut v_m_9013_: *mut LeanObject,
    mut v_a_9014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9015_: *mut LeanObject = core::ptr::null_mut();
    v___x_9015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_9013_, v_a_9014_);
    return v___x_9015_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_9016_: *mut LeanObject,
    mut v_m_9017_: *mut LeanObject,
    mut v_a_9018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9019_: *mut LeanObject = core::ptr::null_mut();
    v_res_9019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_9016_, v_m_9017_, v_a_9018_);
    lean_dec_ref(v_a_9018_);
    lean_dec_ref(v_m_9017_);
    return v_res_9019_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(
    mut v_00_u03b2_9020_: *mut LeanObject,
    mut v_x_9021_: *mut LeanObject,
    mut v_x_9022_: usize,
    mut v_x_9023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    v___x_9024_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_9021_, v_x_9022_, v_x_9023_);
    return v___x_9024_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_9025_: *mut LeanObject,
    mut v_x_9026_: *mut LeanObject,
    mut v_x_9027_: *mut LeanObject,
    mut v_x_9028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2653__boxed_9029_: usize = 0;
    let mut v_res_9030_: *mut LeanObject = core::ptr::null_mut();
    v_x_2653__boxed_9029_ = lean_unbox_usize(v_x_9027_);
    lean_dec(v_x_9027_);
    v_res_9030_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_9025_, v_x_9026_, v_x_2653__boxed_9029_, v_x_9028_);
    lean_dec_ref(v_x_9028_);
    lean_dec_ref(v_x_9026_);
    return v_res_9030_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_9031_: *mut LeanObject,
    mut v_a_9032_: *mut LeanObject,
    mut v_x_9033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9034_: *mut LeanObject = core::ptr::null_mut();
    v___x_9034_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_9032_, v_x_9033_);
    return v___x_9034_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_9035_: *mut LeanObject,
    mut v_a_9036_: *mut LeanObject,
    mut v_x_9037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9038_: *mut LeanObject = core::ptr::null_mut();
    v_res_9038_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_9035_, v_a_9036_, v_x_9037_);
    lean_dec(v_x_9037_);
    lean_dec_ref(v_a_9036_);
    return v_res_9038_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_9039_: *mut LeanObject,
    mut v_keys_9040_: *mut LeanObject,
    mut v_vals_9041_: *mut LeanObject,
    mut v_heq_9042_: *mut LeanObject,
    mut v_i_9043_: *mut LeanObject,
    mut v_k_9044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9045_: *mut LeanObject = core::ptr::null_mut();
    v___x_9045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_9040_, v_vals_9041_, v_i_9043_, v_k_9044_);
    return v___x_9045_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_9046_: *mut LeanObject,
    mut v_keys_9047_: *mut LeanObject,
    mut v_vals_9048_: *mut LeanObject,
    mut v_heq_9049_: *mut LeanObject,
    mut v_i_9050_: *mut LeanObject,
    mut v_k_9051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9052_: *mut LeanObject = core::ptr::null_mut();
    v_res_9052_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_9046_, v_keys_9047_, v_vals_9048_, v_heq_9049_, v_i_9050_, v_k_9051_);
    lean_dec_ref(v_k_9051_);
    lean_dec_ref(v_vals_9048_);
    lean_dec_ref(v_keys_9047_);
    return v_res_9052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_ElimInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_instInhabitedElimInfo_default = _init_l_Lean_Meta_instInhabitedElimInfo_default();
    lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo_default);
    l_Lean_Meta_instInhabitedElimInfo = _init_l_Lean_Meta_instInhabitedElimInfo();
    lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo);
    l_Lean_Meta_instInhabitedCustomEliminators_default =
        _init_l_Lean_Meta_instInhabitedCustomEliminators_default();
    lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators_default);
    l_Lean_Meta_instInhabitedCustomEliminators = _init_l_Lean_Meta_instInhabitedCustomEliminators();
    lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators);
    res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_customEliminatorExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_customEliminatorExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_ElimInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_ElimInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_ElimInfo(builtin);
}
