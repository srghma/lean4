// Lean compiler output
// Module: Lean.Elab.Tactic.Repeat
// Imports: Lean.Meta.Tactic.Repeat Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_SavedState_restore___redArg,
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_evalTacticAtRaw___boxed,
    l_Lean_Elab_Tactic_getGoals___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_setGoals___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withoutRecover___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Tactic::Repeat::{
    initialize_Lean_Meta_Tactic_Repeat, runtime_initialize_Lean_Meta_Tactic_Repeat,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__3_value: LeanStringObject<14> =
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
        m_data: [116, 97, 99, 116, 105, 99, 82, 101, 112, 101, 97, 116, 95, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalRepeat___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value) as *mut LeanObject,
        16592576665728214421 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalRepeat___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__5_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalRepeat___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalRepeat___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut LeanObject,16974933337766822453 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 112, 101, 97, 116, 39, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value)
                as *mut LeanObject,
            4309869778282365895 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut LeanObject,14670036760128995796 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 15 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut LeanObject,((( 15 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 114, 101, 112, 101, 97, 116, 49, 39, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0]};
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value: LeanStringObject<9> =
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
        m_data: [114, 101, 112, 101, 97, 116, 49, 39, 0],
    };
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value)
                as *mut LeanObject,
            9350812594340289083 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 49, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut LeanObject,11253676299092030557 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1100_ = lean_box(0);
    v___x_1101_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1102_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    lean_ctor_set(v___x_1102_, 1, v___x_1100_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0);
    v___x_1105_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(
    mut v___y_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1107_: *mut LeanObject = core::ptr::null_mut();
    v_res_1107_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v_res_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(
    mut v_00_u03b1_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    v___x_1118_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v___x_1118_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(
    mut v_00_u03b1_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1129_: *mut LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(
        v_00_u03b1_1119_,
        v___y_1120_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
        v___y_1125_,
        v___y_1126_,
        v___y_1127_,
    );
    lean_dec(v___y_1127_);
    lean_dec_ref(v___y_1126_);
    lean_dec(v___y_1125_);
    lean_dec_ref(v___y_1124_);
    lean_dec(v___y_1123_);
    lean_dec_ref(v___y_1122_);
    lean_dec(v___y_1121_);
    lean_dec_ref(v___y_1120_);
    return v_res_1129_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(
    mut v___x_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1147_: u8 = 0;
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut v_unused_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: u8 = 0;
    let mut v_a_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1166_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1140_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_1132_,
                    v___y_1134_,
                    v___y_1136_,
                    v___y_1138_,
                );
                if lean_obj_tag(v___x_1140_) == 0 {
                    v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
                    lean_inc(v_a_1141_);
                    lean_dec_ref_known(v___x_1140_, 1);
                    lean_inc(v___x_1130_);
                    v___x_1142_ = l_Lean_Elab_Tactic_evalTactic(
                        v___x_1130_,
                        v___y_1131_,
                        v___y_1132_,
                        v___y_1133_,
                        v___y_1134_,
                        v___y_1135_,
                        v___y_1136_,
                        v___y_1137_,
                        v___y_1138_,
                    );
                    if lean_obj_tag(v___x_1142_) == 0 {
                        lean_dec_ref_known(v___x_1142_, 1);
                        lean_dec(v_a_1141_);
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_1130_);
                        v_a_1144_ = lean_ctor_get(v___x_1142_, 0);
                        lean_inc(v_a_1144_);
                        v___x_1145_ = lean_box(0);
                        v___x_1157_ = l_Lean_Exception_isInterrupt(v_a_1144_);
                        if v___x_1157_ == 0 {
                            v___x_1158_ = l_Lean_Exception_isRuntime(v_a_1144_);
                            v___y_1147_ = v___x_1158_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1144_);
                            v___y_1147_ = v___x_1157_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1130_);
                    v_a_1159_ = lean_ctor_get(v___x_1140_, 0);
                    v_isSharedCheck_1166_ = (!lean_is_exclusive(v___x_1140_)) as u8;
                    if v_isSharedCheck_1166_ == 0 {
                        v___x_1161_ = v___x_1140_;
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1159_);
                        lean_dec(v___x_1140_);
                        v___x_1161_ = lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1147_ == 0 {
                    lean_dec_ref_known(v___x_1142_, 1);
                    v___x_1148_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_1141_,
                        v___y_1147_,
                        v___y_1132_,
                        v___y_1133_,
                        v___y_1134_,
                        v___y_1135_,
                        v___y_1136_,
                        v___y_1137_,
                        v___y_1138_,
                    );
                    if lean_obj_tag(v___x_1148_) == 0 {
                        v_isSharedCheck_1155_ = (!lean_is_exclusive(v___x_1148_)) as u8;
                        if v_isSharedCheck_1155_ == 0 {
                            v_unused_1156_ = lean_ctor_get(v___x_1148_, 0);
                            lean_dec(v_unused_1156_);
                            v___x_1150_ = v___x_1148_;
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1148_);
                            v___x_1150_ = lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1148_;
                    }
                } else {
                    lean_dec(v_a_1141_);
                    return v___x_1142_;
                }
            }
            2 => {
                if v_isShared_1151_ == 0 {
                    lean_ctor_set(v___x_1150_, 0, v___x_1145_);
                    v___x_1153_ = v___x_1150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1145_);
                    v___x_1153_ = v_reuseFailAlloc_1154_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1153_;
            }
            4 => {
                if v_isShared_1162_ == 0 {
                    v___x_1164_ = v___x_1161_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
                    v___x_1164_ = v_reuseFailAlloc_1165_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg___boxed(
    mut v___x_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1177_: *mut LeanObject = core::ptr::null_mut();
    v_res_1177_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    lean_dec(v___y_1175_);
    lean_dec_ref(v___y_1174_);
    lean_dec(v___y_1173_);
    lean_dec_ref(v___y_1172_);
    lean_dec(v___y_1171_);
    lean_dec_ref(v___y_1170_);
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    return v_res_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat___lam__0(
    mut v___x_1178_: *mut LeanObject,
    mut v___x_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
    mut v___y_1181_: *mut LeanObject,
    mut v___y_1182_: *mut LeanObject,
    mut v___y_1183_: *mut LeanObject,
    mut v___y_1184_: *mut LeanObject,
    mut v___y_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut v_unused_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1189_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1178_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
                if lean_obj_tag(v___x_1189_) == 0 {
                    v_isSharedCheck_1196_ = (!lean_is_exclusive(v___x_1189_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v_unused_1197_ = lean_ctor_get(v___x_1189_, 0);
                        lean_dec(v_unused_1197_);
                        v___x_1191_ = v___x_1189_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1189_);
                        v___x_1191_ = lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1189_;
                }
            }
            1 => {
                if v_isShared_1192_ == 0 {
                    lean_ctor_set(v___x_1191_, 0, v___x_1179_);
                    v___x_1194_ = v___x_1191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1179_);
                    v___x_1194_ = v_reuseFailAlloc_1195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed(
    mut v___x_1198_: *mut LeanObject,
    mut v___x_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1209_: *mut LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Lean_Elab_Tactic_evalRepeat___lam__0(
        v___x_1198_,
        v___x_1199_,
        v___y_1200_,
        v___y_1201_,
        v___y_1202_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
        v___y_1206_,
        v___y_1207_,
    );
    lean_dec(v___y_1207_);
    lean_dec_ref(v___y_1206_);
    lean_dec(v___y_1205_);
    lean_dec_ref(v___y_1204_);
    lean_dec(v___y_1203_);
    lean_dec_ref(v___y_1202_);
    lean_dec(v___y_1201_);
    lean_dec_ref(v___y_1200_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat(
    mut v_stx_1225_: *mut LeanObject,
    mut v_a_1226_: *mut LeanObject,
    mut v_a_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_a_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
    mut v_a_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v___x_1235_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    lean_inc(v_stx_1225_);
    v___x_1236_ = l_Lean_Syntax_isOfKind(v_stx_1225_, v___x_1235_);
    if v___x_1236_ == 0 {
        let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_1225_);
        v___x_1237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
        return v___x_1237_;
    } else {
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        v___x_1238_ = lean_unsigned_to_nat(1);
        v___x_1239_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_1238_);
        lean_dec(v_stx_1225_);
        v___x_1240_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
        lean_inc(v___x_1239_);
        v___x_1241_ = l_Lean_Syntax_isOfKind(v___x_1239_, v___x_1240_);
        if v___x_1241_ == 0 {
            let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1239_);
            v___x_1242_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
            return v___x_1242_;
        } else {
            let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
            v___x_1243_ = lean_box(0);
            v___f_1244_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed as *mut core::ffi::c_void,
                11,
                2,
            );
            lean_closure_set(v___f_1244_, 0, v___x_1239_);
            lean_closure_set(v___f_1244_, 1, v___x_1243_);
            v___x_1245_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                v___f_1244_,
                v_a_1226_,
                v_a_1227_,
                v_a_1228_,
                v_a_1229_,
                v_a_1230_,
                v_a_1231_,
                v_a_1232_,
                v_a_1233_,
            );
            return v___x_1245_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat___boxed(
    mut v_stx_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
    mut v_a_1251_: *mut LeanObject,
    mut v_a_1252_: *mut LeanObject,
    mut v_a_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1256_: *mut LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Lean_Elab_Tactic_evalRepeat(
        v_stx_1246_,
        v_a_1247_,
        v_a_1248_,
        v_a_1249_,
        v_a_1250_,
        v_a_1251_,
        v_a_1252_,
        v_a_1253_,
        v_a_1254_,
    );
    lean_dec(v_a_1254_);
    lean_dec_ref(v_a_1253_);
    lean_dec(v_a_1252_);
    lean_dec_ref(v_a_1251_);
    lean_dec(v_a_1250_);
    lean_dec_ref(v_a_1249_);
    lean_dec(v_a_1248_);
    lean_dec_ref(v_a_1247_);
    return v_res_1256_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(
    mut v___x_1257_: *mut LeanObject,
    mut v_inst_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1269_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1257_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    return v___x_1269_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(
    mut v___x_1270_: *mut LeanObject,
    mut v_inst_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1282_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(
            v___x_1270_,
            v_inst_1271_,
            v_a_1272_,
            v___y_1273_,
            v___y_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
            v___y_1278_,
            v___y_1279_,
            v___y_1280_,
        );
    lean_dec(v___y_1280_);
    lean_dec_ref(v___y_1279_);
    lean_dec(v___y_1278_);
    lean_dec_ref(v___y_1277_);
    lean_dec(v___y_1276_);
    lean_dec_ref(v___y_1275_);
    lean_dec(v___y_1274_);
    lean_dec_ref(v___y_1273_);
    return v_res_1282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1()
-> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1292_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    v___x_1293_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2;
    v___x_1294_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRepeat___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1295_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1291_,
        v___x_1292_,
        v___x_1293_,
        v___x_1294_,
    );
    return v___x_1295_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___boxed(
    mut v_a_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    return v_res_1297_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_x_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_a_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___y_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_unused_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1342_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_a_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: u8 = 0;
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v_a_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_a_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1308_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_1300_,
                    v___y_1302_,
                    v___y_1304_,
                    v___y_1306_,
                );
                if lean_obj_tag(v___x_1308_) == 0 {
                    v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
                    lean_inc(v_a_1309_);
                    lean_dec_ref_known(v___x_1308_, 1);
                    v___x_1310_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_1300_,
                        v___y_1302_,
                        v___y_1304_,
                        v___y_1306_,
                    );
                    if lean_obj_tag(v___x_1310_) == 0 {
                        v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
                        lean_inc(v_a_1311_);
                        lean_dec_ref_known(v___x_1310_, 1);
                        lean_inc(v___y_1306_);
                        lean_inc_ref(v___y_1305_);
                        lean_inc(v___y_1304_);
                        lean_inc_ref(v___y_1303_);
                        lean_inc(v___y_1302_);
                        lean_inc_ref(v___y_1301_);
                        lean_inc(v___y_1300_);
                        lean_inc_ref(v___y_1299_);
                        v___x_1312_ = lean_apply_9(
                            v_x_1298_,
                            v___y_1299_,
                            v___y_1300_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_1312_) == 0 {
                            lean_dec(v_a_1311_);
                            lean_dec(v_a_1309_);
                            v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1321_ == 0 {
                                v___x_1315_ = v___x_1312_;
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1313_);
                                lean_dec(v___x_1312_);
                                v___x_1315_ = lean_box(0);
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1322_ = lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1360_ = (!lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1360_ == 0 {
                                v___x_1324_ = v___x_1312_;
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1322_);
                                lean_dec(v___x_1312_);
                                v___x_1324_ = lean_box(0);
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1309_);
                        lean_dec_ref(v_x_1298_);
                        v_a_1361_ = lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1368_ = (!lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1363_ = v___x_1310_;
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_1361_);
                            lean_dec(v___x_1310_);
                            v___x_1363_ = lean_box(0);
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_1298_);
                    v_a_1369_ = lean_ctor_get(v___x_1308_, 0);
                    v_isSharedCheck_1376_ = (!lean_is_exclusive(v___x_1308_)) as u8;
                    if v_isSharedCheck_1376_ == 0 {
                        v___x_1371_ = v___x_1308_;
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_1369_);
                        lean_dec(v___x_1308_);
                        v___x_1371_ = lean_box(0);
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1317_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v_a_1313_);
                if v_isShared_1316_ == 0 {
                    lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1319_;
            }
            3 => {
                v___x_1358_ = l_Lean_Exception_isInterrupt(v_a_1322_);
                if v___x_1358_ == 0 {
                    lean_inc(v_a_1322_);
                    v___x_1359_ = l_Lean_Exception_isRuntime(v_a_1322_);
                    v___y_1327_ = v___x_1359_;
                    state = 4;
                    continue;
                } else {
                    v___y_1327_ = v___x_1358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_1327_ == 0 {
                    lean_del_object(v___x_1324_);
                    lean_dec(v_a_1322_);
                    v___x_1328_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_1311_,
                        v___y_1327_,
                        v___y_1300_,
                        v___y_1301_,
                        v___y_1302_,
                        v___y_1303_,
                        v___y_1304_,
                        v___y_1305_,
                        v___y_1306_,
                    );
                    if lean_obj_tag(v___x_1328_) == 0 {
                        lean_dec_ref_known(v___x_1328_, 1);
                        v___x_1329_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                            v_a_1309_,
                            v___y_1327_,
                            v___y_1300_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                        );
                        if lean_obj_tag(v___x_1329_) == 0 {
                            v_isSharedCheck_1337_ = (!lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1337_ == 0 {
                                v_unused_1338_ = lean_ctor_get(v___x_1329_, 0);
                                lean_dec(v_unused_1338_);
                                v___x_1331_ = v___x_1329_;
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_1329_);
                                v___x_1331_ = lean_box(0);
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_1339_ = lean_ctor_get(v___x_1329_, 0);
                            v_isSharedCheck_1346_ = (!lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1346_ == 0 {
                                v___x_1341_ = v___x_1329_;
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1339_);
                                lean_dec(v___x_1329_);
                                v___x_1341_ = lean_box(0);
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1309_);
                        v_a_1347_ = lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1354_ = (!lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1354_ == 0 {
                            v___x_1349_ = v___x_1328_;
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1347_);
                            lean_dec(v___x_1328_);
                            v___x_1349_ = lean_box(0);
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1311_);
                    lean_dec(v_a_1309_);
                    if v_isShared_1325_ == 0 {
                        v___x_1356_ = v___x_1324_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1322_);
                        v___x_1356_ = v_reuseFailAlloc_1357_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1333_ = lean_box(0);
                if v_isShared_1332_ == 0 {
                    lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1335_;
            }
            7 => {
                if v_isShared_1342_ == 0 {
                    v___x_1344_ = v___x_1341_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
                    v___x_1344_ = v_reuseFailAlloc_1345_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1344_;
            }
            9 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1352_;
            }
            11 => {
                return v___x_1356_;
            }
            12 => {
                if v_isShared_1364_ == 0 {
                    v___x_1366_ = v___x_1363_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1366_;
            }
            14 => {
                if v_isShared_1372_ == 0 {
                    v___x_1374_ = v___x_1371_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_x_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1387_: *mut LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
    lean_dec(v___y_1385_);
    lean_dec_ref(v___y_1384_);
    lean_dec(v___y_1383_);
    lean_dec_ref(v___y_1382_);
    lean_dec(v___y_1381_);
    lean_dec_ref(v___y_1380_);
    lean_dec(v___y_1379_);
    lean_dec_ref(v___y_1378_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(
    mut v_keys_1388_: *mut LeanObject,
    mut v_i_1389_: *mut LeanObject,
    mut v_k_1390_: *mut LeanObject,
) -> u8 {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v_k_x27_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1391_ = lean_array_get_size(v_keys_1388_);
                v___x_1392_ = lean_nat_dec_lt(v_i_1389_, v___x_1391_);
                if v___x_1392_ == 0 {
                    lean_dec(v_i_1389_);
                    return v___x_1392_;
                } else {
                    v_k_x27_1393_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1389_);
                    v___x_1394_ = l_Lean_instBEqMVarId_beq(v_k_1390_, v_k_x27_1393_);
                    if v___x_1394_ == 0 {
                        v___x_1395_ = lean_unsigned_to_nat(1);
                        v___x_1396_ = lean_nat_add(v_i_1389_, v___x_1395_);
                        lean_dec(v_i_1389_);
                        v_i_1389_ = v___x_1396_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_1389_);
                        return v___x_1394_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(
    mut v_keys_1398_: *mut LeanObject,
    mut v_i_1399_: *mut LeanObject,
    mut v_k_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1401_: u8 = 0;
    let mut v_r_1402_: *mut LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1398_, v_i_1399_, v_k_1400_);
    lean_dec(v_k_1400_);
    lean_dec_ref(v_keys_1398_);
    v_r_1402_ = lean_box((v_res_1401_) as usize);
    return v_r_1402_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0()
-> usize {
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: usize = 0;
    v___x_1403_ = 5usize;
    v___x_1404_ = 1usize;
    v___x_1405_ = lean_usize_shift_left(v___x_1404_, v___x_1403_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1()
-> usize {
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: usize = 0;
    v___x_1406_ = 1usize;
    v___x_1407_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0);
    v___x_1408_ = lean_usize_sub(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(
    mut v_x_1409_: *mut LeanObject,
    mut v_x_1410_: usize,
    mut v_x_1411_: *mut LeanObject,
) -> u8 {
    let mut v_es_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: usize = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v_j_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v_node_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v_ks_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1409_) == 0 {
                    v_es_1412_ = lean_ctor_get(v_x_1409_, 0);
                    v___x_1413_ = lean_box(2);
                    v___x_1414_ = 5usize;
                    v___x_1415_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1);
                    v___x_1416_ = lean_usize_land(v_x_1410_, v___x_1415_);
                    v_j_1417_ = lean_usize_to_nat(v___x_1416_);
                    v___x_1418_ = lean_array_get_borrowed(v___x_1413_, v_es_1412_, v_j_1417_);
                    lean_dec(v_j_1417_);
                    match lean_obj_tag(v___x_1418_) {
                        0 => {
                            v_key_1419_ = lean_ctor_get(v___x_1418_, 0);
                            v___x_1420_ = l_Lean_instBEqMVarId_beq(v_x_1411_, v_key_1419_);
                            return v___x_1420_;
                        }
                        1 => {
                            v_node_1421_ = lean_ctor_get(v___x_1418_, 0);
                            v___x_1422_ = lean_usize_shift_right(v_x_1410_, v___x_1414_);
                            v_x_1409_ = v_node_1421_;
                            v_x_1410_ = v___x_1422_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1424_ = 0;
                            return v___x_1424_;
                        }
                    }
                } else {
                    v_ks_1425_ = lean_ctor_get(v_x_1409_, 0);
                    v___x_1426_ = lean_unsigned_to_nat(0);
                    v___x_1427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_1425_, v___x_1426_, v_x_1411_);
                    return v___x_1427_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(
    mut v_x_1428_: *mut LeanObject,
    mut v_x_1429_: *mut LeanObject,
    mut v_x_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4769__boxed_1431_: usize = 0;
    let mut v_res_1432_: u8 = 0;
    let mut v_r_1433_: *mut LeanObject = core::ptr::null_mut();
    v_x_4769__boxed_1431_ = lean_unbox_usize(v_x_1429_);
    lean_dec(v_x_1429_);
    v_res_1432_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1428_, v_x_4769__boxed_1431_, v_x_1430_);
    lean_dec(v_x_1430_);
    lean_dec_ref(v_x_1428_);
    v_r_1433_ = lean_box((v_res_1432_) as usize);
    return v_r_1433_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_x_1434_: *mut LeanObject,
    mut v_x_1435_: *mut LeanObject,
) -> u8 {
    let mut v___x_1436_: u64 = 0;
    let mut v___x_1437_: usize = 0;
    let mut v___x_1438_: u8 = 0;
    v___x_1436_ = l_Lean_instHashableMVarId_hash(v_x_1435_);
    v___x_1437_ = lean_uint64_to_usize(v___x_1436_);
    v___x_1438_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1434_, v___x_1437_, v_x_1435_);
    return v___x_1438_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_x_1439_: *mut LeanObject,
    mut v_x_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1439_, v_x_1440_);
    lean_dec(v_x_1440_);
    lean_dec_ref(v_x_1439_);
    v_r_1442_ = lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(
    mut v_mvarId_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v___x_1446_ = lean_st_ref_get(v___y_1444_);
    v_mctx_1447_ = lean_ctor_get(v___x_1446_, 0);
    lean_inc_ref(v_mctx_1447_);
    lean_dec(v___x_1446_);
    v_eAssignment_1448_ = lean_ctor_get(v_mctx_1447_, 8);
    lean_inc_ref(v_eAssignment_1448_);
    lean_dec_ref(v_mctx_1447_);
    v___x_1449_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_1448_, v_mvarId_1443_);
    lean_dec_ref(v_eAssignment_1448_);
    v___x_1450_ = lean_box((v___x_1449_) as usize);
    v___x_1451_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1451_, 0, v___x_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_mvarId_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1452_, v___y_1453_);
    lean_dec(v___y_1453_);
    lean_dec(v_mvarId_1452_);
    return v_res_1455_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1456_: *mut LeanObject,
    mut v_x_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1457_) == 0 {
                    return v_x_1456_;
                } else {
                    v_head_1458_ = lean_ctor_get(v_x_1457_, 0);
                    lean_inc(v_head_1458_);
                    v_tail_1459_ = lean_ctor_get(v_x_1457_, 1);
                    lean_inc(v_tail_1459_);
                    lean_dec_ref_known(v_x_1457_, 2);
                    v___x_1460_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_x_1456_,
                        v_head_1458_,
                    );
                    v_x_1456_ = v___x_1460_;
                    v_x_1457_ = v_tail_1459_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(
    mut v_f_1462_: *mut LeanObject,
    mut v_a_1463_: *mut LeanObject,
    mut v_a_1464_: u8,
    mut v_a_1465_: *mut LeanObject,
    mut v_a_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v_zero_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1495_: u8 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1465_) == 0 {
                    if lean_obj_tag(v_a_1466_) == 0 {
                        lean_dec(v_a_1463_);
                        lean_dec_ref(v_f_1462_);
                        v___x_1477_ = lean_box((v_a_1464_) as usize);
                        v___x_1478_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1478_, 0, v___x_1477_);
                        lean_ctor_set(v___x_1478_, 1, v_a_1467_);
                        v___x_1479_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1479_, 0, v___x_1478_);
                        return v___x_1479_;
                    } else {
                        v_head_1480_ = lean_ctor_get(v_a_1466_, 0);
                        lean_inc(v_head_1480_);
                        v_tail_1481_ = lean_ctor_get(v_a_1466_, 1);
                        lean_inc(v_tail_1481_);
                        lean_dec_ref_known(v_a_1466_, 2);
                        v_a_1465_ = v_head_1480_;
                        v_a_1466_ = v_tail_1481_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_head_1483_ = lean_ctor_get(v_a_1465_, 0);
                    v_tail_1484_ = lean_ctor_get(v_a_1465_, 1);
                    v_isSharedCheck_1527_ = (!lean_is_exclusive(v_a_1465_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1486_ = v_a_1465_;
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1484_);
                        lean_inc(v_head_1483_);
                        lean_dec(v_a_1465_);
                        v___x_1486_ = lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1488_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_1483_, v___y_1473_);
                v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
                v_isSharedCheck_1526_ = (!lean_is_exclusive(v___x_1488_)) as u8;
                if v_isSharedCheck_1526_ == 0 {
                    v___x_1491_ = v___x_1488_;
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1489_);
                    lean_dec(v___x_1488_);
                    v___x_1491_ = lean_box(0);
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1493_ = (lean_unbox(v_a_1489_) as u8);
                lean_dec(v_a_1489_);
                if v___x_1493_ == 0 {
                    v_zero_1494_ = lean_unsigned_to_nat(0);
                    v_isZero_1495_ = lean_nat_dec_eq(v_a_1463_, v_zero_1494_);
                    if v_isZero_1495_ == 1 {
                        lean_del_object(v___x_1486_);
                        lean_dec(v_a_1463_);
                        lean_dec_ref(v_f_1462_);
                        v___x_1496_ = lean_array_push(v_a_1467_, v_head_1483_);
                        v___x_1497_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                            v___x_1496_,
                            v_tail_1484_,
                        );
                        v___x_1498_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_1497_, v_a_1466_);
                        v___x_1499_ = lean_box((v_a_1464_) as usize);
                        v___x_1500_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                        lean_ctor_set(v___x_1500_, 1, v___x_1498_);
                        if v_isShared_1492_ == 0 {
                            lean_ctor_set(v___x_1491_, 0, v___x_1500_);
                            v___x_1502_ = v___x_1491_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                            v___x_1502_ = v_reuseFailAlloc_1503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1491_);
                        lean_inc_ref(v_f_1462_);
                        lean_inc(v_head_1483_);
                        v___x_1504_ = lean_apply_1(v_f_1462_, v_head_1483_);
                        v___x_1505_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1504_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
                        if lean_obj_tag(v___x_1505_) == 0 {
                            v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
                            lean_inc(v_a_1506_);
                            lean_dec_ref_known(v___x_1505_, 1);
                            v_one_1507_ = lean_unsigned_to_nat(1);
                            v_n_1508_ = lean_nat_sub(v_a_1463_, v_one_1507_);
                            lean_dec(v_a_1463_);
                            if lean_obj_tag(v_a_1506_) == 0 {
                                lean_del_object(v___x_1486_);
                                v___x_1509_ = lean_array_push(v_a_1467_, v_head_1483_);
                                v_a_1463_ = v_n_1508_;
                                v_a_1465_ = v_tail_1484_;
                                v_a_1467_ = v___x_1509_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_head_1483_);
                                v_val_1511_ = lean_ctor_get(v_a_1506_, 0);
                                lean_inc(v_val_1511_);
                                lean_dec_ref_known(v_a_1506_, 1);
                                v___x_1512_ = 1;
                                if v_isShared_1487_ == 0 {
                                    lean_ctor_set(v___x_1486_, 1, v_a_1466_);
                                    lean_ctor_set(v___x_1486_, 0, v_tail_1484_);
                                    v___x_1514_ = v___x_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_tail_1484_);
                                    lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1466_);
                                    v___x_1514_ = v_reuseFailAlloc_1516_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_1486_);
                            lean_dec(v_tail_1484_);
                            lean_dec(v_head_1483_);
                            lean_dec_ref(v_a_1467_);
                            lean_dec(v_a_1466_);
                            lean_dec(v_a_1463_);
                            lean_dec_ref(v_f_1462_);
                            v_a_1517_ = lean_ctor_get(v___x_1505_, 0);
                            v_isSharedCheck_1524_ = (!lean_is_exclusive(v___x_1505_)) as u8;
                            if v_isSharedCheck_1524_ == 0 {
                                v___x_1519_ = v___x_1505_;
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1517_);
                                lean_dec(v___x_1505_);
                                v___x_1519_ = lean_box(0);
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_1491_);
                    lean_del_object(v___x_1486_);
                    lean_dec(v_head_1483_);
                    v_a_1465_ = v_tail_1484_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1502_;
            }
            4 => {
                v_a_1463_ = v_n_1508_;
                v_a_1464_ = v___x_1512_;
                v_a_1465_ = v_val_1511_;
                v_a_1466_ = v___x_1514_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1___boxed(
    mut v_f_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
    mut v_a_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
    mut v___y_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4854__boxed_1543_: u8 = 0;
    let mut v_res_1544_: *mut LeanObject = core::ptr::null_mut();
    v_a_4854__boxed_1543_ = (lean_unbox(v_a_1530_) as u8);
    v_res_1544_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1528_, v_a_1529_, v_a_4854__boxed_1543_, v_a_1531_, v_a_1532_, v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
    lean_dec(v___y_1541_);
    lean_dec_ref(v___y_1540_);
    lean_dec(v___y_1539_);
    lean_dec_ref(v___y_1538_);
    lean_dec(v___y_1537_);
    lean_dec_ref(v___y_1536_);
    lean_dec(v___y_1535_);
    lean_dec_ref(v___y_1534_);
    return v_res_1544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(
    mut v_as_1545_: *mut LeanObject,
    mut v_i_1546_: usize,
    mut v_stop_1547_: usize,
    mut v_b_1548_: *mut LeanObject,
    mut v___y_1549_: *mut LeanObject,
    mut v___y_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
    mut v___y_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: usize = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_a_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v_a_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = lean_usize_dec_eq(v_i_1546_, v_stop_1547_);
                if v___x_1563_ == 0 {
                    v___x_1564_ = lean_array_uget_borrowed(v_as_1545_, v_i_1546_);
                    v___x_1567_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_1564_, v___y_1554_);
                    if lean_obj_tag(v___x_1567_) == 0 {
                        v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                        lean_inc(v_a_1568_);
                        lean_dec_ref_known(v___x_1567_, 1);
                        v___x_1569_ = (lean_unbox(v_a_1568_) as u8);
                        lean_dec(v_a_1568_);
                        if v___x_1569_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1559_ = v_b_1548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1570_ = lean_ctor_get(v___x_1567_, 0);
                            lean_inc(v_a_1570_);
                            lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1571_ = (lean_unbox(v_a_1570_) as u8);
                            lean_dec(v_a_1570_);
                            if v___x_1571_ == 0 {
                                v_a_1559_ = v_b_1548_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_1548_);
                            v_a_1572_ = lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1579_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v___x_1574_ = v___x_1567_;
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1572_);
                                lean_dec(v___x_1567_);
                                v___x_1574_ = lean_box(0);
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1580_, 0, v_b_1548_);
                    return v___x_1580_;
                }
            }
            1 => {
                v___x_1560_ = 1usize;
                v___x_1561_ = lean_usize_add(v_i_1546_, v___x_1560_);
                v_i_1546_ = v___x_1561_;
                v_b_1548_ = v_a_1559_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___x_1564_);
                v___x_1566_ = lean_array_push(v_b_1548_, v___x_1564_);
                v_a_1559_ = v___x_1566_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_1575_ == 0 {
                    v___x_1577_ = v___x_1574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
                    v___x_1577_ = v_reuseFailAlloc_1578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3___boxed(
    mut v_as_1581_: *mut LeanObject,
    mut v_i_1582_: *mut LeanObject,
    mut v_stop_1583_: *mut LeanObject,
    mut v_b_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1594_: usize = 0;
    let mut v_stop_boxed_1595_: usize = 0;
    let mut v_res_1596_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1594_ = lean_unbox_usize(v_i_1582_);
    lean_dec(v_i_1582_);
    v_stop_boxed_1595_ = lean_unbox_usize(v_stop_1583_);
    lean_dec(v_stop_1583_);
    v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_1581_, v_i_boxed_1594_, v_stop_boxed_1595_, v_b_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
    lean_dec(v___y_1592_);
    lean_dec_ref(v___y_1591_);
    lean_dec(v___y_1590_);
    lean_dec_ref(v___y_1589_);
    lean_dec(v___y_1588_);
    lean_dec_ref(v___y_1587_);
    lean_dec(v___y_1586_);
    lean_dec_ref(v___y_1585_);
    lean_dec_ref(v_as_1581_);
    return v_res_1596_;
}
pub unsafe fn _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
    v___x_1600_ = lean_array_to_list(v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(
    mut v_f_1601_: *mut LeanObject,
    mut v_goals_1602_: *mut LeanObject,
    mut v_maxIters_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v_fst_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v_____do__lift_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1613_ = 0;
                v___x_1614_ = lean_box(0);
                v___x_1615_ = lean_unsigned_to_nat(0);
                v___x_1616_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
                v___x_1617_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1601_, v_maxIters_1603_, v___x_1613_, v_goals_1602_, v___x_1614_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                if lean_obj_tag(v___x_1617_) == 0 {
                    v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1667_ = (!lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1620_ = v___x_1617_;
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1618_);
                        lean_dec(v___x_1617_);
                        v___x_1620_ = lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1668_ = lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1675_ = (!lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1617_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1668_);
                        lean_dec(v___x_1617_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
                v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
                v_isSharedCheck_1666_ = (!lean_is_exclusive(v_a_1618_)) as u8;
                if v_isSharedCheck_1666_ == 0 {
                    v___x_1625_ = v_a_1618_;
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1623_);
                    lean_inc(v_fst_1622_);
                    lean_dec(v_a_1618_);
                    v___x_1625_ = lean_box(0);
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1636_ = lean_array_get_size(v_snd_1623_);
                v___x_1637_ = lean_nat_dec_lt(v___x_1615_, v___x_1636_);
                if v___x_1637_ == 0 {
                    lean_del_object(v___x_1625_);
                    lean_dec(v_snd_1623_);
                    lean_del_object(v___x_1620_);
                    v___x_1638_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once), _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
                    v___x_1639_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1639_, 0, v_fst_1622_);
                    lean_ctor_set(v___x_1639_, 1, v___x_1638_);
                    v___x_1640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                    return v___x_1640_;
                } else {
                    v___x_1641_ = lean_nat_dec_le(v___x_1636_, v___x_1636_);
                    if v___x_1641_ == 0 {
                        if v___x_1637_ == 0 {
                            lean_dec(v_snd_1623_);
                            v_____do__lift_1628_ = v___x_1616_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1642_ = 0usize;
                            v___x_1643_ = lean_usize_of_nat(v___x_1636_);
                            v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_1623_, v___x_1642_, v___x_1643_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                            lean_dec(v_snd_1623_);
                            if lean_obj_tag(v___x_1644_) == 0 {
                                v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
                                lean_inc(v_a_1645_);
                                lean_dec_ref_known(v___x_1644_, 1);
                                v_____do__lift_1628_ = v_a_1645_;
                                state = 3;
                                continue;
                            } else {
                                lean_del_object(v___x_1625_);
                                lean_dec(v_fst_1622_);
                                lean_del_object(v___x_1620_);
                                v_a_1646_ = lean_ctor_get(v___x_1644_, 0);
                                v_isSharedCheck_1653_ = (!lean_is_exclusive(v___x_1644_)) as u8;
                                if v_isSharedCheck_1653_ == 0 {
                                    v___x_1648_ = v___x_1644_;
                                    v_isShared_1649_ = v_isSharedCheck_1653_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1646_);
                                    lean_dec(v___x_1644_);
                                    v___x_1648_ = lean_box(0);
                                    v_isShared_1649_ = v_isSharedCheck_1653_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1654_ = 0usize;
                        v___x_1655_ = lean_usize_of_nat(v___x_1636_);
                        v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_1623_, v___x_1654_, v___x_1655_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                        lean_dec(v_snd_1623_);
                        if lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
                            lean_inc(v_a_1657_);
                            lean_dec_ref_known(v___x_1656_, 1);
                            v_____do__lift_1628_ = v_a_1657_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_1625_);
                            lean_dec(v_fst_1622_);
                            lean_del_object(v___x_1620_);
                            v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
                            v_isSharedCheck_1665_ = (!lean_is_exclusive(v___x_1656_)) as u8;
                            if v_isSharedCheck_1665_ == 0 {
                                v___x_1660_ = v___x_1656_;
                                v_isShared_1661_ = v_isSharedCheck_1665_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1658_);
                                lean_dec(v___x_1656_);
                                v___x_1660_ = lean_box(0);
                                v_isShared_1661_ = v_isSharedCheck_1665_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1629_ = lean_array_to_list(v_____do__lift_1628_);
                if v_isShared_1626_ == 0 {
                    lean_ctor_set(v___x_1625_, 1, v___x_1629_);
                    v___x_1631_ = v___x_1625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fst_1622_);
                    lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1629_);
                    v___x_1631_ = v_reuseFailAlloc_1635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1621_ == 0 {
                    lean_ctor_set(v___x_1620_, 0, v___x_1631_);
                    v___x_1633_ = v___x_1620_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1633_;
            }
            6 => {
                if v_isShared_1649_ == 0 {
                    v___x_1651_ = v___x_1648_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
                    v___x_1651_ = v_reuseFailAlloc_1652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1651_;
            }
            8 => {
                if v_isShared_1661_ == 0 {
                    v___x_1663_ = v___x_1660_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
                    v___x_1663_ = v_reuseFailAlloc_1664_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1663_;
            }
            10 => {
                if v_isShared_1671_ == 0 {
                    v___x_1673_ = v___x_1670_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
                    v___x_1673_ = v_reuseFailAlloc_1674_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed(
    mut v_f_1676_: *mut LeanObject,
    mut v_goals_1677_: *mut LeanObject,
    mut v_maxIters_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1688_: *mut LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_1676_, v_goals_1677_, v_maxIters_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
    lean_dec(v___y_1686_);
    lean_dec_ref(v___y_1685_);
    lean_dec(v___y_1684_);
    lean_dec_ref(v___y_1683_);
    lean_dec(v___y_1682_);
    lean_dec_ref(v___y_1681_);
    lean_dec(v___y_1680_);
    lean_dec_ref(v___y_1679_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(
    mut v_x_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_1690_: *mut LeanObject = core::ptr::null_mut();
    v_snd_1690_ = lean_ctor_get(v_x_1689_, 1);
    lean_inc(v_snd_1690_);
    return v_snd_1690_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(
    mut v_x_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_1691_);
    lean_dec_ref(v_x_1691_);
    return v_res_1692_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(
    mut v_a_1693_: *mut LeanObject,
    mut v_f_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1702_);
                lean_inc_ref(v___y_1701_);
                lean_inc(v___y_1700_);
                lean_inc_ref(v___y_1699_);
                lean_inc(v___y_1698_);
                lean_inc_ref(v___y_1697_);
                lean_inc(v___y_1696_);
                lean_inc_ref(v___y_1695_);
                v___x_1704_ = lean_apply_9(
                    v_a_1693_,
                    v___y_1695_,
                    v___y_1696_,
                    v___y_1697_,
                    v___y_1698_,
                    v___y_1699_,
                    v___y_1700_,
                    v___y_1701_,
                    v___y_1702_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1704_) == 0 {
                    v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1713_ = (!lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v___x_1707_ = v___x_1704_;
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1705_);
                        lean_dec(v___x_1704_);
                        v___x_1707_ = lean_box(0);
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1694_);
                    v_a_1714_ = lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1721_ = (!lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1721_ == 0 {
                        v___x_1716_ = v___x_1704_;
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1714_);
                        lean_dec(v___x_1704_);
                        v___x_1716_ = lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1709_ = lean_apply_1(v_f_1694_, v_a_1705_);
                if v_isShared_1708_ == 0 {
                    lean_ctor_set(v___x_1707_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1711_;
            }
            3 => {
                if v_isShared_1717_ == 0 {
                    v___x_1719_ = v___x_1716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg___boxed(
    mut v_a_1722_: *mut LeanObject,
    mut v_f_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1733_: *mut LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1722_, v_f_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    lean_dec(v___y_1731_);
    lean_dec_ref(v___y_1730_);
    lean_dec(v___y_1729_);
    lean_dec_ref(v___y_1728_);
    lean_dec(v___y_1727_);
    lean_dec_ref(v___y_1726_);
    lean_dec(v___y_1725_);
    lean_dec_ref(v___y_1724_);
    return v_res_1733_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(
    mut v_f_1735_: *mut LeanObject,
    mut v_goals_1736_: *mut LeanObject,
    mut v_maxIters_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___f_1747_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0;
    v___x_1748_ = lean_alloc_closure(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed as *mut core::ffi::c_void, 12, 3);
    lean_closure_set(v___x_1748_, 0, v_f_1735_);
    lean_closure_set(v___x_1748_, 1, v_goals_1736_);
    lean_closure_set(v___x_1748_, 2, v_maxIters_1737_);
    v___x_1749_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_1748_, v___f_1747_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
    return v___x_1749_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(
    mut v_f_1750_: *mut LeanObject,
    mut v_goals_1751_: *mut LeanObject,
    mut v_maxIters_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(
        v_f_1750_,
        v_goals_1751_,
        v_maxIters_1752_,
        v___y_1753_,
        v___y_1754_,
        v___y_1755_,
        v___y_1756_,
        v___y_1757_,
        v___y_1758_,
        v___y_1759_,
        v___y_1760_,
    );
    lean_dec(v___y_1760_);
    lean_dec_ref(v___y_1759_);
    lean_dec(v___y_1758_);
    lean_dec_ref(v___y_1757_);
    lean_dec(v___y_1756_);
    lean_dec_ref(v___y_1755_);
    lean_dec(v___y_1754_);
    lean_dec_ref(v___y_1753_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat_x27(
    mut v_stx_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_a_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
                lean_inc(v_stx_1769_);
                v___x_1780_ = l_Lean_Syntax_isOfKind(v_stx_1769_, v___x_1779_);
                if v___x_1780_ == 0 {
                    lean_dec(v_stx_1769_);
                    v___x_1781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_1781_;
                } else {
                    v___x_1782_ = lean_unsigned_to_nat(1);
                    v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1769_, v___x_1782_);
                    lean_dec(v_stx_1769_);
                    v___x_1784_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    lean_inc(v___x_1783_);
                    v___x_1785_ = l_Lean_Syntax_isOfKind(v___x_1783_, v___x_1784_);
                    if v___x_1785_ == 0 {
                        lean_dec(v___x_1783_);
                        v___x_1786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_1786_;
                    } else {
                        v___x_1787_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_1771_);
                        if lean_obj_tag(v___x_1787_) == 0 {
                            v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
                            lean_inc(v_a_1788_);
                            lean_dec_ref_known(v___x_1787_, 1);
                            v___x_1789_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            lean_closure_set(v___x_1789_, 0, v___x_1783_);
                            v___x_1790_ = lean_unsigned_to_nat(100000);
                            v___x_1791_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_1789_, v_a_1788_, v___x_1790_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
                            if lean_obj_tag(v___x_1791_) == 0 {
                                v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
                                lean_inc(v_a_1792_);
                                lean_dec_ref_known(v___x_1791_, 1);
                                v___x_1793_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_1792_, v_a_1771_);
                                return v___x_1793_;
                            } else {
                                v_a_1794_ = lean_ctor_get(v___x_1791_, 0);
                                v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1791_)) as u8;
                                if v_isSharedCheck_1801_ == 0 {
                                    v___x_1796_ = v___x_1791_;
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1794_);
                                    lean_dec(v___x_1791_);
                                    v___x_1796_ = lean_box(0);
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_1783_);
                            v_a_1802_ = lean_ctor_get(v___x_1787_, 0);
                            v_isSharedCheck_1809_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1787_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1802_);
                                lean_dec(v___x_1787_);
                                v___x_1804_ = lean_box(0);
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1799_;
            }
            3 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat_x27___boxed(
    mut v_stx_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1820_: *mut LeanObject = core::ptr::null_mut();
    v_res_1820_ = l_Lean_Elab_Tactic_evalRepeat_x27(
        v_stx_1810_,
        v_a_1811_,
        v_a_1812_,
        v_a_1813_,
        v_a_1814_,
        v_a_1815_,
        v_a_1816_,
        v_a_1817_,
        v_a_1818_,
    );
    lean_dec(v_a_1818_);
    lean_dec_ref(v_a_1817_);
    lean_dec(v_a_1816_);
    lean_dec_ref(v_a_1815_);
    lean_dec(v_a_1814_);
    lean_dec_ref(v_a_1813_);
    lean_dec(v_a_1812_);
    lean_dec_ref(v_a_1811_);
    return v_res_1820_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(
    mut v_00_u03b1_1821_: *mut LeanObject,
    mut v_00_u03b2_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_f_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1823_, v_f_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    return v___x_1834_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(
    mut v_00_u03b1_1835_: *mut LeanObject,
    mut v_00_u03b2_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_f_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_1835_, v_00_u03b2_1836_, v_a_1837_, v_f_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    lean_dec(v___y_1846_);
    lean_dec_ref(v___y_1845_);
    lean_dec(v___y_1844_);
    lean_dec_ref(v___y_1843_);
    lean_dec(v___y_1842_);
    lean_dec_ref(v___y_1841_);
    lean_dec(v___y_1840_);
    lean_dec_ref(v___y_1839_);
    return v_res_1848_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_x_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1860_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1861_: *mut LeanObject,
    mut v_x_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1872_: *mut LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1861_, v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
    lean_dec(v___y_1870_);
    lean_dec_ref(v___y_1869_);
    lean_dec(v___y_1868_);
    lean_dec_ref(v___y_1867_);
    lean_dec(v___y_1866_);
    lean_dec_ref(v___y_1865_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(
    mut v_mvarId_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1873_, v___y_1879_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(
    mut v_mvarId_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1894_: *mut LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
    lean_dec(v___y_1892_);
    lean_dec_ref(v___y_1891_);
    lean_dec(v___y_1890_);
    lean_dec_ref(v___y_1889_);
    lean_dec(v___y_1888_);
    lean_dec_ref(v___y_1887_);
    lean_dec(v___y_1886_);
    lean_dec_ref(v___y_1885_);
    lean_dec(v_mvarId_1884_);
    return v_res_1894_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1895_: *mut LeanObject,
    mut v_x_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
) -> u8 {
    let mut v___x_1898_: u8 = 0;
    v___x_1898_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1899_: *mut LeanObject,
    mut v_x_1900_: *mut LeanObject,
    mut v_x_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: u8 = 0;
    let mut v_r_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1899_, v_x_1900_, v_x_1901_);
    lean_dec(v_x_1901_);
    lean_dec_ref(v_x_1900_);
    v_r_1903_ = lean_box((v_res_1902_) as usize);
    return v_r_1903_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(
    mut v_00_u03b2_1904_: *mut LeanObject,
    mut v_x_1905_: *mut LeanObject,
    mut v_x_1906_: usize,
    mut v_x_1907_: *mut LeanObject,
) -> u8 {
    let mut v___x_1908_: u8 = 0;
    v___x_1908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1905_, v_x_1906_, v_x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(
    mut v_00_u03b2_1909_: *mut LeanObject,
    mut v_x_1910_: *mut LeanObject,
    mut v_x_1911_: *mut LeanObject,
    mut v_x_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5520__boxed_1913_: usize = 0;
    let mut v_res_1914_: u8 = 0;
    let mut v_r_1915_: *mut LeanObject = core::ptr::null_mut();
    v_x_5520__boxed_1913_ = lean_unbox_usize(v_x_1911_);
    lean_dec(v_x_1911_);
    v_res_1914_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_1909_, v_x_1910_, v_x_5520__boxed_1913_, v_x_1912_);
    lean_dec(v_x_1912_);
    lean_dec_ref(v_x_1910_);
    v_r_1915_ = lean_box((v_res_1914_) as usize);
    return v_r_1915_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(
    mut v_00_u03b2_1916_: *mut LeanObject,
    mut v_keys_1917_: *mut LeanObject,
    mut v_vals_1918_: *mut LeanObject,
    mut v_heq_1919_: *mut LeanObject,
    mut v_i_1920_: *mut LeanObject,
    mut v_k_1921_: *mut LeanObject,
) -> u8 {
    let mut v___x_1922_: u8 = 0;
    v___x_1922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1917_, v_i_1920_, v_k_1921_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(
    mut v_00_u03b2_1923_: *mut LeanObject,
    mut v_keys_1924_: *mut LeanObject,
    mut v_vals_1925_: *mut LeanObject,
    mut v_heq_1926_: *mut LeanObject,
    mut v_i_1927_: *mut LeanObject,
    mut v_k_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: u8 = 0;
    let mut v_r_1930_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_1923_, v_keys_1924_, v_vals_1925_, v_heq_1926_, v_i_1927_, v_k_1928_);
    lean_dec(v_k_1928_);
    lean_dec_ref(v_vals_1925_);
    lean_dec_ref(v_keys_1924_);
    v_r_1930_ = lean_box((v_res_1929_) as usize);
    return v_r_1930_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1()
-> *mut LeanObject {
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1939_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
    v___x_1940_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1941_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRepeat_x27___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1942_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1938_,
        v___x_1939_,
        v___x_1940_,
        v___x_1941_,
    );
    return v___x_1942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___boxed(
    mut v_a_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_res_1944_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    return v_res_1944_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3()
-> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1971_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1972_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6;
    v___x_1973_ = l_Lean_addBuiltinDeclarationRanges(v___x_1971_, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    return v_res_1975_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(
    mut v_msgData_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    v___x_1982_ = lean_st_ref_get(v___y_1980_);
    v_env_1983_ = lean_ctor_get(v___x_1982_, 0);
    lean_inc_ref(v_env_1983_);
    lean_dec(v___x_1982_);
    v___x_1984_ = lean_st_ref_get(v___y_1978_);
    v_mctx_1985_ = lean_ctor_get(v___x_1984_, 0);
    lean_inc_ref(v_mctx_1985_);
    lean_dec(v___x_1984_);
    v_lctx_1986_ = lean_ctor_get(v___y_1977_, 2);
    v_options_1987_ = lean_ctor_get(v___y_1979_, 2);
    lean_inc_ref(v_options_1987_);
    lean_inc_ref(v_lctx_1986_);
    v___x_1988_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1988_, 0, v_env_1983_);
    lean_ctor_set(v___x_1988_, 1, v_mctx_1985_);
    lean_ctor_set(v___x_1988_, 2, v_lctx_1986_);
    lean_ctor_set(v___x_1988_, 3, v_options_1987_);
    v___x_1989_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1989_, 0, v___x_1988_);
    lean_ctor_set(v___x_1989_, 1, v_msgData_1976_);
    v___x_1990_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1990_, 0, v___x_1989_);
    return v___x_1990_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1997_: *mut LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    lean_dec(v___y_1995_);
    lean_dec_ref(v___y_1994_);
    lean_dec(v___y_1993_);
    lean_dec_ref(v___y_1992_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(
    mut v_msg_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2004_ = lean_ctor_get(v___y_2001_, 5);
                v___x_2005_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
                v_isSharedCheck_2014_ = (!lean_is_exclusive(v___x_2005_)) as u8;
                if v_isSharedCheck_2014_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2006_);
                    lean_dec(v___x_2005_);
                    v___x_2008_ = lean_box(0);
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2004_);
                v___x_2010_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2010_, 0, v_ref_2004_);
                lean_ctor_set(v___x_2010_, 1, v_a_2006_);
                if v_isShared_2009_ == 0 {
                    lean_ctor_set_tag(v___x_2008_, 1);
                    lean_ctor_set(v___x_2008_, 0, v___x_2010_);
                    v___x_2012_ = v___x_2008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg___boxed(
    mut v_msg_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2021_: *mut LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
    lean_dec(v___y_2019_);
    lean_dec_ref(v___y_2018_);
    lean_dec(v___y_2017_);
    lean_dec_ref(v___y_2016_);
    return v_res_2021_;
}
pub unsafe fn _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    v___x_2023_ =
        l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0;
    v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(
    mut v_f_2025_: *mut LeanObject,
    mut v_goals_2026_: *mut LeanObject,
    mut v_maxIters_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
    mut v___y_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v_fst_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v_snd_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2037_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_2025_, v_goals_2026_, v_maxIters_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
                if lean_obj_tag(v___x_2037_) == 0 {
                    v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2050_ = (!lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2040_ = v___x_2037_;
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2038_);
                        lean_dec(v___x_2037_);
                        v___x_2040_ = lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2051_ = lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2037_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2051_);
                        lean_dec(v___x_2037_);
                        v___x_2053_ = lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2042_ = lean_ctor_get(v_a_2038_, 0);
                v___x_2043_ = (lean_unbox(v_fst_2042_) as u8);
                if v___x_2043_ == 1 {
                    v_snd_2044_ = lean_ctor_get(v_a_2038_, 1);
                    lean_inc(v_snd_2044_);
                    lean_dec(v_a_2038_);
                    if v_isShared_2041_ == 0 {
                        lean_ctor_set(v___x_2040_, 0, v_snd_2044_);
                        v___x_2046_ = v___x_2040_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_snd_2044_);
                        v___x_2046_ = v_reuseFailAlloc_2047_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2040_);
                    lean_dec(v_a_2038_);
                    v___x_2048_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once), _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
                    v___x_2049_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v___x_2048_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
                    return v___x_2049_;
                }
            }
            2 => {
                return v___x_2046_;
            }
            3 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___boxed(
    mut v_f_2059_: *mut LeanObject,
    mut v_goals_2060_: *mut LeanObject,
    mut v_maxIters_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2071_: *mut LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(
        v_f_2059_,
        v_goals_2060_,
        v_maxIters_2061_,
        v___y_2062_,
        v___y_2063_,
        v___y_2064_,
        v___y_2065_,
        v___y_2066_,
        v___y_2067_,
        v___y_2068_,
        v___y_2069_,
    );
    lean_dec(v___y_2069_);
    lean_dec_ref(v___y_2068_);
    lean_dec(v___y_2067_);
    lean_dec_ref(v___y_2066_);
    lean_dec(v___y_2065_);
    lean_dec_ref(v___y_2064_);
    lean_dec(v___y_2063_);
    lean_dec_ref(v___y_2062_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat1_x27(
    mut v_stx_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2088_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
                lean_inc(v_stx_2078_);
                v___x_2089_ = l_Lean_Syntax_isOfKind(v_stx_2078_, v___x_2088_);
                if v___x_2089_ == 0 {
                    lean_dec(v_stx_2078_);
                    v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_2090_;
                } else {
                    v___x_2091_ = lean_unsigned_to_nat(1);
                    v___x_2092_ = l_Lean_Syntax_getArg(v_stx_2078_, v___x_2091_);
                    lean_dec(v_stx_2078_);
                    v___x_2093_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    lean_inc(v___x_2092_);
                    v___x_2094_ = l_Lean_Syntax_isOfKind(v___x_2092_, v___x_2093_);
                    if v___x_2094_ == 0 {
                        lean_dec(v___x_2092_);
                        v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_2095_;
                    } else {
                        v___x_2096_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_2080_);
                        if lean_obj_tag(v___x_2096_) == 0 {
                            v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
                            lean_inc(v_a_2097_);
                            lean_dec_ref_known(v___x_2096_, 1);
                            v___x_2098_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            lean_closure_set(v___x_2098_, 0, v___x_2092_);
                            v___x_2099_ = lean_unsigned_to_nat(100000);
                            v___x_2100_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_2098_, v_a_2097_, v___x_2099_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
                            if lean_obj_tag(v___x_2100_) == 0 {
                                v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
                                lean_inc(v_a_2101_);
                                lean_dec_ref_known(v___x_2100_, 1);
                                v___x_2102_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_2101_, v_a_2080_);
                                return v___x_2102_;
                            } else {
                                v_a_2103_ = lean_ctor_get(v___x_2100_, 0);
                                v_isSharedCheck_2110_ = (!lean_is_exclusive(v___x_2100_)) as u8;
                                if v_isSharedCheck_2110_ == 0 {
                                    v___x_2105_ = v___x_2100_;
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2103_);
                                    lean_dec(v___x_2100_);
                                    v___x_2105_ = lean_box(0);
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2092_);
                            v_a_2111_ = lean_ctor_get(v___x_2096_, 0);
                            v_isSharedCheck_2118_ = (!lean_is_exclusive(v___x_2096_)) as u8;
                            if v_isSharedCheck_2118_ == 0 {
                                v___x_2113_ = v___x_2096_;
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2111_);
                                lean_dec(v___x_2096_);
                                v___x_2113_ = lean_box(0);
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2106_ == 0 {
                    v___x_2108_ = v___x_2105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
                    v___x_2108_ = v_reuseFailAlloc_2109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2108_;
            }
            3 => {
                if v_isShared_2114_ == 0 {
                    v___x_2116_ = v___x_2113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat1_x27___boxed(
    mut v_stx_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
    mut v_a_2125_: *mut LeanObject,
    mut v_a_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2129_: *mut LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Lean_Elab_Tactic_evalRepeat1_x27(
        v_stx_2119_,
        v_a_2120_,
        v_a_2121_,
        v_a_2122_,
        v_a_2123_,
        v_a_2124_,
        v_a_2125_,
        v_a_2126_,
        v_a_2127_,
    );
    lean_dec(v_a_2127_);
    lean_dec_ref(v_a_2126_);
    lean_dec(v_a_2125_);
    lean_dec_ref(v_a_2124_);
    lean_dec(v_a_2123_);
    lean_dec_ref(v_a_2122_);
    lean_dec(v_a_2121_);
    lean_dec_ref(v_a_2120_);
    return v_res_2129_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(
    mut v_00_u03b1_2130_: *mut LeanObject,
    mut v_msg_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___x_2141_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2131_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(
    mut v_00_u03b1_2142_: *mut LeanObject,
    mut v_msg_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_2142_, v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    lean_dec(v___y_2151_);
    lean_dec_ref(v___y_2150_);
    lean_dec(v___y_2149_);
    lean_dec_ref(v___y_2148_);
    lean_dec(v___y_2147_);
    lean_dec_ref(v___y_2146_);
    lean_dec(v___y_2145_);
    lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1()
-> *mut LeanObject {
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2162_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
    v___x_2163_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2164_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRepeat1_x27___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2165_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2161_,
        v___x_2162_,
        v___x_2163_,
        v___x_2164_,
    );
    return v___x_2165_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___boxed(
    mut v_a_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2167_: *mut LeanObject = core::ptr::null_mut();
    v_res_2167_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    return v_res_2167_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3()
-> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2194_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2195_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6;
    v___x_2196_ = l_Lean_addBuiltinDeclarationRanges(v___x_2194_, v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(
    mut v_a_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2198_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    return v_res_2198_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Repeat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Repeat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Repeat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Repeat(builtin);
}
