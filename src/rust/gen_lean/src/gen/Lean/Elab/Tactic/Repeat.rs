// Lean compiler output
// Module: Lean.Elab.Tactic.Repeat
// Imports: Lean.Meta.Tactic.Repeat Lean.Elab.Tactic.Basic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_array_uget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
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
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__3_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            16592576665728214421 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__5_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut crate::leanh::LeanObject,16974933337766822453 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4309869778282365895 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut crate::leanh::LeanObject,14670036760128995796 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 114, 101, 112, 101, 97, 116, 49, 39, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0]};
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9350812594340289083 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 49, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut crate::leanh::LeanObject,11253676299092030557 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = crate::leanh::lean_box(0);
    v___x_1101_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1102_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    crate::leanh::lean_ctor_set(v___x_1102_, 1, v___x_1100_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0);
    v___x_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(
    mut v___y_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v_res_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(
    mut v_00_u03b1_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v___x_1118_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(
    mut v_00_u03b1_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1127_);
    crate::leanh::lean_dec_ref(v___y_1126_);
    crate::leanh::lean_dec(v___y_1125_);
    crate::leanh::lean_dec_ref(v___y_1124_);
    crate::leanh::lean_dec(v___y_1123_);
    crate::leanh::lean_dec_ref(v___y_1122_);
    crate::leanh::lean_dec(v___y_1121_);
    crate::leanh::lean_dec_ref(v___y_1120_);
    return v_res_1129_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(
    mut v___x_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1147_: u8 = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut v_unused_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: u8 = 0;
    let mut v_a_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_1140_) == 0 {
                    v_a_1141_ = crate::leanh::lean_ctor_get(v___x_1140_, 0);
                    crate::leanh::lean_inc(v_a_1141_);
                    crate::leanh::lean_dec_ref_known(v___x_1140_, 1);
                    crate::leanh::lean_inc(v___x_1130_);
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
                    if crate::leanh::lean_obj_tag(v___x_1142_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1142_, 1);
                        crate::leanh::lean_dec(v_a_1141_);
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1130_);
                        v_a_1144_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                        crate::leanh::lean_inc(v_a_1144_);
                        v___x_1145_ = crate::leanh::lean_box(0);
                        v___x_1157_ = l_Lean_Exception_isInterrupt(v_a_1144_);
                        if v___x_1157_ == 0 {
                            v___x_1158_ = l_Lean_Exception_isRuntime(v_a_1144_);
                            v___y_1147_ = v___x_1158_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1144_);
                            v___y_1147_ = v___x_1157_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1130_);
                    v_a_1159_ = crate::leanh::lean_ctor_get(v___x_1140_, 0);
                    v_isSharedCheck_1166_ = (!crate::leanh::lean_is_exclusive(v___x_1140_)) as u8;
                    if v_isSharedCheck_1166_ == 0 {
                        v___x_1161_ = v___x_1140_;
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1159_);
                        crate::leanh::lean_dec(v___x_1140_);
                        v___x_1161_ = crate::leanh::lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1147_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1142_, 1);
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
                    if crate::leanh::lean_obj_tag(v___x_1148_) == 0 {
                        v_isSharedCheck_1155_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1148_)) as u8;
                        if v_isSharedCheck_1155_ == 0 {
                            v_unused_1156_ = crate::leanh::lean_ctor_get(v___x_1148_, 0);
                            crate::leanh::lean_dec(v_unused_1156_);
                            v___x_1150_ = v___x_1148_;
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1148_);
                            v___x_1150_ = crate::leanh::lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1148_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1141_);
                    return v___x_1142_;
                }
            }
            2 => {
                if v_isShared_1151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1145_);
                    v___x_1153_ = v___x_1150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1145_);
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
                    v_reuseFailAlloc_1165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
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
    mut v___x_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    crate::leanh::lean_dec(v___y_1175_);
    crate::leanh::lean_dec_ref(v___y_1174_);
    crate::leanh::lean_dec(v___y_1173_);
    crate::leanh::lean_dec_ref(v___y_1172_);
    crate::leanh::lean_dec(v___y_1171_);
    crate::leanh::lean_dec_ref(v___y_1170_);
    crate::leanh::lean_dec(v___y_1169_);
    crate::leanh::lean_dec_ref(v___y_1168_);
    return v_res_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat___lam__0(
    mut v___x_1178_: *mut crate::leanh::LeanObject,
    mut v___x_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut v_unused_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1189_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1178_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
                if crate::leanh::lean_obj_tag(v___x_1189_) == 0 {
                    v_isSharedCheck_1196_ = (!crate::leanh::lean_is_exclusive(v___x_1189_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v_unused_1197_ = crate::leanh::lean_ctor_get(v___x_1189_, 0);
                        crate::leanh::lean_dec(v_unused_1197_);
                        v___x_1191_ = v___x_1189_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1189_);
                        v___x_1191_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1191_, 0, v___x_1179_);
                    v___x_1194_ = v___x_1191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1179_);
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
    mut v___x_1198_: *mut crate::leanh::LeanObject,
    mut v___x_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1207_);
    crate::leanh::lean_dec_ref(v___y_1206_);
    crate::leanh::lean_dec(v___y_1205_);
    crate::leanh::lean_dec_ref(v___y_1204_);
    crate::leanh::lean_dec(v___y_1203_);
    crate::leanh::lean_dec_ref(v___y_1202_);
    crate::leanh::lean_dec(v___y_1201_);
    crate::leanh::lean_dec_ref(v___y_1200_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat(
    mut v_stx_1225_: *mut crate::leanh::LeanObject,
    mut v_a_1226_: *mut crate::leanh::LeanObject,
    mut v_a_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v___x_1235_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    crate::leanh::lean_inc(v_stx_1225_);
    v___x_1236_ = l_Lean_Syntax_isOfKind(v_stx_1225_, v___x_1235_);
    if v___x_1236_ == 0 {
        let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_1225_);
        v___x_1237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
        return v___x_1237_;
    } else {
        let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        v___x_1238_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1239_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_1238_);
        crate::leanh::lean_dec(v_stx_1225_);
        v___x_1240_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
        crate::leanh::lean_inc(v___x_1239_);
        v___x_1241_ = l_Lean_Syntax_isOfKind(v___x_1239_, v___x_1240_);
        if v___x_1241_ == 0 {
            let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1239_);
            v___x_1242_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
            return v___x_1242_;
        } else {
            let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1243_ = crate::leanh::lean_box(0);
            v___f_1244_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed as *mut core::ffi::c_void,
                11,
                2,
            );
            crate::leanh::lean_closure_set(v___f_1244_, 0, v___x_1239_);
            crate::leanh::lean_closure_set(v___f_1244_, 1, v___x_1243_);
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
    mut v_stx_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1254_);
    crate::leanh::lean_dec_ref(v_a_1253_);
    crate::leanh::lean_dec(v_a_1252_);
    crate::leanh::lean_dec_ref(v_a_1251_);
    crate::leanh::lean_dec(v_a_1250_);
    crate::leanh::lean_dec_ref(v_a_1249_);
    crate::leanh::lean_dec(v_a_1248_);
    crate::leanh::lean_dec_ref(v_a_1247_);
    return v_res_1256_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(
    mut v___x_1257_: *mut crate::leanh::LeanObject,
    mut v_inst_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1257_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    return v___x_1269_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(
    mut v___x_1270_: *mut crate::leanh::LeanObject,
    mut v_inst_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1280_);
    crate::leanh::lean_dec_ref(v___y_1279_);
    crate::leanh::lean_dec(v___y_1278_);
    crate::leanh::lean_dec_ref(v___y_1277_);
    crate::leanh::lean_dec(v___y_1276_);
    crate::leanh::lean_dec_ref(v___y_1275_);
    crate::leanh::lean_dec(v___y_1274_);
    crate::leanh::lean_dec_ref(v___y_1273_);
    return v_res_1282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1292_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    v___x_1293_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2;
    v___x_1294_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    return v_res_1297_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_x_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_a_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___y_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_unused_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1342_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: u8 = 0;
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v_a_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_a_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_1308_) == 0 {
                    v_a_1309_ = crate::leanh::lean_ctor_get(v___x_1308_, 0);
                    crate::leanh::lean_inc(v_a_1309_);
                    crate::leanh::lean_dec_ref_known(v___x_1308_, 1);
                    v___x_1310_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_1300_,
                        v___y_1302_,
                        v___y_1304_,
                        v___y_1306_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1310_) == 0 {
                        v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                        crate::leanh::lean_inc(v_a_1311_);
                        crate::leanh::lean_dec_ref_known(v___x_1310_, 1);
                        crate::leanh::lean_inc(v___y_1306_);
                        crate::leanh::lean_inc_ref(v___y_1305_);
                        crate::leanh::lean_inc(v___y_1304_);
                        crate::leanh::lean_inc_ref(v___y_1303_);
                        crate::leanh::lean_inc(v___y_1302_);
                        crate::leanh::lean_inc_ref(v___y_1301_);
                        crate::leanh::lean_inc(v___y_1300_);
                        crate::leanh::lean_inc_ref(v___y_1299_);
                        v___x_1312_ = crate::leanh::lean_apply_9(
                            v_x_1298_,
                            v___y_1299_,
                            v___y_1300_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_1312_) == 0 {
                            crate::leanh::lean_dec(v_a_1311_);
                            crate::leanh::lean_dec(v_a_1309_);
                            v_a_1313_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1321_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1321_ == 0 {
                                v___x_1315_ = v___x_1312_;
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1313_);
                                crate::leanh::lean_dec(v___x_1312_);
                                v___x_1315_ = crate::leanh::lean_box(0);
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1322_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1360_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1360_ == 0 {
                                v___x_1324_ = v___x_1312_;
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1322_);
                                crate::leanh::lean_dec(v___x_1312_);
                                v___x_1324_ = crate::leanh::lean_box(0);
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1309_);
                        crate::leanh::lean_dec_ref(v_x_1298_);
                        v_a_1361_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1368_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1363_ = v___x_1310_;
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1361_);
                            crate::leanh::lean_dec(v___x_1310_);
                            v___x_1363_ = crate::leanh::lean_box(0);
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1298_);
                    v_a_1369_ = crate::leanh::lean_ctor_get(v___x_1308_, 0);
                    v_isSharedCheck_1376_ = (!crate::leanh::lean_is_exclusive(v___x_1308_)) as u8;
                    if v_isSharedCheck_1376_ == 0 {
                        v___x_1371_ = v___x_1308_;
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1369_);
                        crate::leanh::lean_dec(v___x_1308_);
                        v___x_1371_ = crate::leanh::lean_box(0);
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1317_, 0, v_a_1313_);
                if v_isShared_1316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
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
                    crate::leanh::lean_inc(v_a_1322_);
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
                    crate::leanh::lean_del_object(v___x_1324_);
                    crate::leanh::lean_dec(v_a_1322_);
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
                    if crate::leanh::lean_obj_tag(v___x_1328_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1328_, 1);
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
                        if crate::leanh::lean_obj_tag(v___x_1329_) == 0 {
                            v_isSharedCheck_1337_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1337_ == 0 {
                                v_unused_1338_ = crate::leanh::lean_ctor_get(v___x_1329_, 0);
                                crate::leanh::lean_dec(v_unused_1338_);
                                v___x_1331_ = v___x_1329_;
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1329_);
                                v___x_1331_ = crate::leanh::lean_box(0);
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_1339_ = crate::leanh::lean_ctor_get(v___x_1329_, 0);
                            v_isSharedCheck_1346_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1346_ == 0 {
                                v___x_1341_ = v___x_1329_;
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1339_);
                                crate::leanh::lean_dec(v___x_1329_);
                                v___x_1341_ = crate::leanh::lean_box(0);
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1309_);
                        v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1354_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1354_ == 0 {
                            v___x_1349_ = v___x_1328_;
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1347_);
                            crate::leanh::lean_dec(v___x_1328_);
                            v___x_1349_ = crate::leanh::lean_box(0);
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1311_);
                    crate::leanh::lean_dec(v_a_1309_);
                    if v_isShared_1325_ == 0 {
                        v___x_1356_ = v___x_1324_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1322_);
                        v___x_1356_ = v_reuseFailAlloc_1357_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1333_ = crate::leanh::lean_box(0);
                if v_isShared_1332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
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
                    v_reuseFailAlloc_1345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
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
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
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
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
                    v_reuseFailAlloc_1375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
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
    mut v_x_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
    crate::leanh::lean_dec(v___y_1385_);
    crate::leanh::lean_dec_ref(v___y_1384_);
    crate::leanh::lean_dec(v___y_1383_);
    crate::leanh::lean_dec_ref(v___y_1382_);
    crate::leanh::lean_dec(v___y_1381_);
    crate::leanh::lean_dec_ref(v___y_1380_);
    crate::leanh::lean_dec(v___y_1379_);
    crate::leanh::lean_dec_ref(v___y_1378_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(
    mut v_keys_1388_: *mut crate::leanh::LeanObject,
    mut v_i_1389_: *mut crate::leanh::LeanObject,
    mut v_k_1390_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v_k_x27_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1391_ = lean_array_get_size(v_keys_1388_);
                v___x_1392_ = lean_nat_dec_lt(v_i_1389_, v___x_1391_);
                if v___x_1392_ == 0 {
                    crate::leanh::lean_dec(v_i_1389_);
                    return v___x_1392_;
                } else {
                    v_k_x27_1393_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1389_);
                    v___x_1394_ = l_Lean_instBEqMVarId_beq(v_k_1390_, v_k_x27_1393_);
                    if v___x_1394_ == 0 {
                        v___x_1395_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1396_ = lean_nat_add(v_i_1389_, v___x_1395_);
                        crate::leanh::lean_dec(v_i_1389_);
                        v_i_1389_ = v___x_1396_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1389_);
                        return v___x_1394_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(
    mut v_keys_1398_: *mut crate::leanh::LeanObject,
    mut v_i_1399_: *mut crate::leanh::LeanObject,
    mut v_k_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1401_: u8 = 0;
    let mut v_r_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1398_, v_i_1399_, v_k_1400_);
    crate::leanh::lean_dec(v_k_1400_);
    crate::leanh::lean_dec_ref(v_keys_1398_);
    v_r_1402_ = crate::leanh::lean_box((v_res_1401_) as usize);
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
    v___x_1407_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0);
    v___x_1408_ = lean_usize_sub(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(
    mut v_x_1409_: *mut crate::leanh::LeanObject,
    mut v_x_1410_: usize,
    mut v_x_1411_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: usize = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v_j_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v_node_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v_ks_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1409_) == 0 {
                    v_es_1412_ = crate::leanh::lean_ctor_get(v_x_1409_, 0);
                    v___x_1413_ = crate::leanh::lean_box(2);
                    v___x_1414_ = 5usize;
                    v___x_1415_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1);
                    v___x_1416_ = lean_usize_land(v_x_1410_, v___x_1415_);
                    v_j_1417_ = lean_usize_to_nat(v___x_1416_);
                    v___x_1418_ = lean_array_get_borrowed(v___x_1413_, v_es_1412_, v_j_1417_);
                    crate::leanh::lean_dec(v_j_1417_);
                    match crate::leanh::lean_obj_tag(v___x_1418_) {
                        0 => {
                            v_key_1419_ = crate::leanh::lean_ctor_get(v___x_1418_, 0);
                            v___x_1420_ = l_Lean_instBEqMVarId_beq(v_x_1411_, v_key_1419_);
                            return v___x_1420_;
                        }
                        1 => {
                            v_node_1421_ = crate::leanh::lean_ctor_get(v___x_1418_, 0);
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
                    v_ks_1425_ = crate::leanh::lean_ctor_get(v_x_1409_, 0);
                    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_1425_, v___x_1426_, v_x_1411_);
                    return v___x_1427_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v_x_1429_: *mut crate::leanh::LeanObject,
    mut v_x_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4769__boxed_1431_: usize = 0;
    let mut v_res_1432_: u8 = 0;
    let mut v_r_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4769__boxed_1431_ = crate::leanh::lean_unbox_usize(v_x_1429_);
    crate::leanh::lean_dec(v_x_1429_);
    v_res_1432_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1428_, v_x_4769__boxed_1431_, v_x_1430_);
    crate::leanh::lean_dec(v_x_1430_);
    crate::leanh::lean_dec_ref(v_x_1428_);
    v_r_1433_ = crate::leanh::lean_box((v_res_1432_) as usize);
    return v_r_1433_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_x_1434_: *mut crate::leanh::LeanObject,
    mut v_x_1435_: *mut crate::leanh::LeanObject,
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
    mut v_x_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1439_, v_x_1440_);
    crate::leanh::lean_dec(v_x_1440_);
    crate::leanh::lean_dec_ref(v_x_1439_);
    v_r_1442_ = crate::leanh::lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(
    mut v_mvarId_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = lean_st_ref_get(v___y_1444_);
    v_mctx_1447_ = crate::leanh::lean_ctor_get(v___x_1446_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1447_);
    crate::leanh::lean_dec(v___x_1446_);
    v_eAssignment_1448_ = crate::leanh::lean_ctor_get(v_mctx_1447_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_1448_);
    crate::leanh::lean_dec_ref(v_mctx_1447_);
    v___x_1449_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_1448_, v_mvarId_1443_);
    crate::leanh::lean_dec_ref(v_eAssignment_1448_);
    v___x_1450_ = crate::leanh::lean_box((v___x_1449_) as usize);
    v___x_1451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_mvarId_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1452_, v___y_1453_);
    crate::leanh::lean_dec(v___y_1453_);
    crate::leanh::lean_dec(v_mvarId_1452_);
    return v_res_1455_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1457_) == 0 {
                    return v_x_1456_;
                } else {
                    v_head_1458_ = crate::leanh::lean_ctor_get(v_x_1457_, 0);
                    crate::leanh::lean_inc(v_head_1458_);
                    v_tail_1459_ = crate::leanh::lean_ctor_get(v_x_1457_, 1);
                    crate::leanh::lean_inc(v_tail_1459_);
                    crate::leanh::lean_dec_ref_known(v_x_1457_, 2);
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
    mut v_f_1462_: *mut crate::leanh::LeanObject,
    mut v_a_1463_: *mut crate::leanh::LeanObject,
    mut v_a_1464_: u8,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_a_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v_zero_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1495_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1465_) == 0 {
                    if crate::leanh::lean_obj_tag(v_a_1466_) == 0 {
                        crate::leanh::lean_dec(v_a_1463_);
                        crate::leanh::lean_dec_ref(v_f_1462_);
                        v___x_1477_ = crate::leanh::lean_box((v_a_1464_) as usize);
                        v___x_1478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
                        crate::leanh::lean_ctor_set(v___x_1478_, 1, v_a_1467_);
                        v___x_1479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1478_);
                        return v___x_1479_;
                    } else {
                        v_head_1480_ = crate::leanh::lean_ctor_get(v_a_1466_, 0);
                        crate::leanh::lean_inc(v_head_1480_);
                        v_tail_1481_ = crate::leanh::lean_ctor_get(v_a_1466_, 1);
                        crate::leanh::lean_inc(v_tail_1481_);
                        crate::leanh::lean_dec_ref_known(v_a_1466_, 2);
                        v_a_1465_ = v_head_1480_;
                        v_a_1466_ = v_tail_1481_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_head_1483_ = crate::leanh::lean_ctor_get(v_a_1465_, 0);
                    v_tail_1484_ = crate::leanh::lean_ctor_get(v_a_1465_, 1);
                    v_isSharedCheck_1527_ = (!crate::leanh::lean_is_exclusive(v_a_1465_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1486_ = v_a_1465_;
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1484_);
                        crate::leanh::lean_inc(v_head_1483_);
                        crate::leanh::lean_dec(v_a_1465_);
                        v___x_1486_ = crate::leanh::lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1488_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_1483_, v___y_1473_);
                v_a_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                v_isSharedCheck_1526_ = (!crate::leanh::lean_is_exclusive(v___x_1488_)) as u8;
                if v_isSharedCheck_1526_ == 0 {
                    v___x_1491_ = v___x_1488_;
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1489_);
                    crate::leanh::lean_dec(v___x_1488_);
                    v___x_1491_ = crate::leanh::lean_box(0);
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1493_ = (crate::leanh::lean_unbox(v_a_1489_) as u8);
                crate::leanh::lean_dec(v_a_1489_);
                if v___x_1493_ == 0 {
                    v_zero_1494_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_1495_ = lean_nat_dec_eq(v_a_1463_, v_zero_1494_);
                    if v_isZero_1495_ == 1 {
                        crate::leanh::lean_del_object(v___x_1486_);
                        crate::leanh::lean_dec(v_a_1463_);
                        crate::leanh::lean_dec_ref(v_f_1462_);
                        v___x_1496_ = lean_array_push(v_a_1467_, v_head_1483_);
                        v___x_1497_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                            v___x_1496_,
                            v_tail_1484_,
                        );
                        v___x_1498_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_1497_, v_a_1466_);
                        v___x_1499_ = crate::leanh::lean_box((v_a_1464_) as usize);
                        v___x_1500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                        crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1498_);
                        if v_isShared_1492_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1491_, 0, v___x_1500_);
                            v___x_1502_ = v___x_1491_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1503_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                            v___x_1502_ = v_reuseFailAlloc_1503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1491_);
                        crate::leanh::lean_inc_ref(v_f_1462_);
                        crate::leanh::lean_inc(v_head_1483_);
                        v___x_1504_ = crate::leanh::lean_apply_1(v_f_1462_, v_head_1483_);
                        v___x_1505_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1504_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
                        if crate::leanh::lean_obj_tag(v___x_1505_) == 0 {
                            v_a_1506_ = crate::leanh::lean_ctor_get(v___x_1505_, 0);
                            crate::leanh::lean_inc(v_a_1506_);
                            crate::leanh::lean_dec_ref_known(v___x_1505_, 1);
                            v_one_1507_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_n_1508_ = lean_nat_sub(v_a_1463_, v_one_1507_);
                            crate::leanh::lean_dec(v_a_1463_);
                            if crate::leanh::lean_obj_tag(v_a_1506_) == 0 {
                                crate::leanh::lean_del_object(v___x_1486_);
                                v___x_1509_ = lean_array_push(v_a_1467_, v_head_1483_);
                                v_a_1463_ = v_n_1508_;
                                v_a_1465_ = v_tail_1484_;
                                v_a_1467_ = v___x_1509_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_head_1483_);
                                v_val_1511_ = crate::leanh::lean_ctor_get(v_a_1506_, 0);
                                crate::leanh::lean_inc(v_val_1511_);
                                crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
                                v___x_1512_ = 1;
                                if v_isShared_1487_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1486_, 1, v_a_1466_);
                                    crate::leanh::lean_ctor_set(v___x_1486_, 0, v_tail_1484_);
                                    v___x_1514_ = v___x_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1516_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1516_,
                                        0,
                                        v_tail_1484_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1516_,
                                        1,
                                        v_a_1466_,
                                    );
                                    v___x_1514_ = v_reuseFailAlloc_1516_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1486_);
                            crate::leanh::lean_dec(v_tail_1484_);
                            crate::leanh::lean_dec(v_head_1483_);
                            crate::leanh::lean_dec_ref(v_a_1467_);
                            crate::leanh::lean_dec(v_a_1466_);
                            crate::leanh::lean_dec(v_a_1463_);
                            crate::leanh::lean_dec_ref(v_f_1462_);
                            v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1505_, 0);
                            v_isSharedCheck_1524_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1505_)) as u8;
                            if v_isSharedCheck_1524_ == 0 {
                                v___x_1519_ = v___x_1505_;
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1517_);
                                crate::leanh::lean_dec(v___x_1505_);
                                v___x_1519_ = crate::leanh::lean_box(0);
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1491_);
                    crate::leanh::lean_del_object(v___x_1486_);
                    crate::leanh::lean_dec(v_head_1483_);
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
                    v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
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
    mut v_f_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4854__boxed_1543_: u8 = 0;
    let mut v_res_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_4854__boxed_1543_ = (crate::leanh::lean_unbox(v_a_1530_) as u8);
    v_res_1544_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1528_, v_a_1529_, v_a_4854__boxed_1543_, v_a_1531_, v_a_1532_, v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
    crate::leanh::lean_dec(v___y_1541_);
    crate::leanh::lean_dec_ref(v___y_1540_);
    crate::leanh::lean_dec(v___y_1539_);
    crate::leanh::lean_dec_ref(v___y_1538_);
    crate::leanh::lean_dec(v___y_1537_);
    crate::leanh::lean_dec_ref(v___y_1536_);
    crate::leanh::lean_dec(v___y_1535_);
    crate::leanh::lean_dec_ref(v___y_1534_);
    return v_res_1544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(
    mut v_as_1545_: *mut crate::leanh::LeanObject,
    mut v_i_1546_: usize,
    mut v_stop_1547_: usize,
    mut v_b_1548_: *mut crate::leanh::LeanObject,
    mut v___y_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: usize = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_a_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v_a_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = lean_usize_dec_eq(v_i_1546_, v_stop_1547_);
                if v___x_1563_ == 0 {
                    v___x_1564_ = lean_array_uget_borrowed(v_as_1545_, v_i_1546_);
                    v___x_1567_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_1564_, v___y_1554_);
                    if crate::leanh::lean_obj_tag(v___x_1567_) == 0 {
                        v_a_1568_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                        crate::leanh::lean_inc(v_a_1568_);
                        crate::leanh::lean_dec_ref_known(v___x_1567_, 1);
                        v___x_1569_ = (crate::leanh::lean_unbox(v_a_1568_) as u8);
                        crate::leanh::lean_dec(v_a_1568_);
                        if v___x_1569_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1559_ = v_b_1548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1570_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                            crate::leanh::lean_inc(v_a_1570_);
                            crate::leanh::lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1571_ = (crate::leanh::lean_unbox(v_a_1570_) as u8);
                            crate::leanh::lean_dec(v_a_1570_);
                            if v___x_1571_ == 0 {
                                v_a_1559_ = v_b_1548_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_1548_);
                            v_a_1572_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1579_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v___x_1574_ = v___x_1567_;
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1572_);
                                crate::leanh::lean_dec(v___x_1567_);
                                v___x_1574_ = crate::leanh::lean_box(0);
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1580_, 0, v_b_1548_);
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
                crate::leanh::lean_inc(v___x_1564_);
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
                    v_reuseFailAlloc_1578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
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
    mut v_as_1581_: *mut crate::leanh::LeanObject,
    mut v_i_1582_: *mut crate::leanh::LeanObject,
    mut v_stop_1583_: *mut crate::leanh::LeanObject,
    mut v_b_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1594_: usize = 0;
    let mut v_stop_boxed_1595_: usize = 0;
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1594_ = crate::leanh::lean_unbox_usize(v_i_1582_);
    crate::leanh::lean_dec(v_i_1582_);
    v_stop_boxed_1595_ = crate::leanh::lean_unbox_usize(v_stop_1583_);
    crate::leanh::lean_dec(v_stop_1583_);
    v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_1581_, v_i_boxed_1594_, v_stop_boxed_1595_, v_b_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
    crate::leanh::lean_dec(v___y_1592_);
    crate::leanh::lean_dec_ref(v___y_1591_);
    crate::leanh::lean_dec(v___y_1590_);
    crate::leanh::lean_dec_ref(v___y_1589_);
    crate::leanh::lean_dec(v___y_1588_);
    crate::leanh::lean_dec_ref(v___y_1587_);
    crate::leanh::lean_dec(v___y_1586_);
    crate::leanh::lean_dec_ref(v___y_1585_);
    crate::leanh::lean_dec_ref(v_as_1581_);
    return v_res_1596_;
}
pub unsafe fn _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
    v___x_1600_ = lean_array_to_list(v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(
    mut v_f_1601_: *mut crate::leanh::LeanObject,
    mut v_goals_1602_: *mut crate::leanh::LeanObject,
    mut v_maxIters_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v_fst_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v_____do__lift_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1613_ = 0;
                v___x_1614_ = crate::leanh::lean_box(0);
                v___x_1615_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1616_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
                v___x_1617_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1601_, v_maxIters_1603_, v___x_1613_, v_goals_1602_, v___x_1614_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                    v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1667_ = (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1620_ = v___x_1617_;
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1618_);
                        crate::leanh::lean_dec(v___x_1617_);
                        v___x_1620_ = crate::leanh::lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1668_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1675_ = (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1617_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1668_);
                        crate::leanh::lean_dec(v___x_1617_);
                        v___x_1670_ = crate::leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1622_ = crate::leanh::lean_ctor_get(v_a_1618_, 0);
                v_snd_1623_ = crate::leanh::lean_ctor_get(v_a_1618_, 1);
                v_isSharedCheck_1666_ = (!crate::leanh::lean_is_exclusive(v_a_1618_)) as u8;
                if v_isSharedCheck_1666_ == 0 {
                    v___x_1625_ = v_a_1618_;
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1623_);
                    crate::leanh::lean_inc(v_fst_1622_);
                    crate::leanh::lean_dec(v_a_1618_);
                    v___x_1625_ = crate::leanh::lean_box(0);
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1636_ = lean_array_get_size(v_snd_1623_);
                v___x_1637_ = lean_nat_dec_lt(v___x_1615_, v___x_1636_);
                if v___x_1637_ == 0 {
                    crate::leanh::lean_del_object(v___x_1625_);
                    crate::leanh::lean_dec(v_snd_1623_);
                    crate::leanh::lean_del_object(v___x_1620_);
                    v___x_1638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once), _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
                    v___x_1639_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1639_, 0, v_fst_1622_);
                    crate::leanh::lean_ctor_set(v___x_1639_, 1, v___x_1638_);
                    v___x_1640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                    return v___x_1640_;
                } else {
                    v___x_1641_ = lean_nat_dec_le(v___x_1636_, v___x_1636_);
                    if v___x_1641_ == 0 {
                        if v___x_1637_ == 0 {
                            crate::leanh::lean_dec(v_snd_1623_);
                            v_____do__lift_1628_ = v___x_1616_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1642_ = 0usize;
                            v___x_1643_ = lean_usize_of_nat(v___x_1636_);
                            v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_1623_, v___x_1642_, v___x_1643_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                            crate::leanh::lean_dec(v_snd_1623_);
                            if crate::leanh::lean_obj_tag(v___x_1644_) == 0 {
                                v_a_1645_ = crate::leanh::lean_ctor_get(v___x_1644_, 0);
                                crate::leanh::lean_inc(v_a_1645_);
                                crate::leanh::lean_dec_ref_known(v___x_1644_, 1);
                                v_____do__lift_1628_ = v_a_1645_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_1625_);
                                crate::leanh::lean_dec(v_fst_1622_);
                                crate::leanh::lean_del_object(v___x_1620_);
                                v_a_1646_ = crate::leanh::lean_ctor_get(v___x_1644_, 0);
                                v_isSharedCheck_1653_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1644_)) as u8;
                                if v_isSharedCheck_1653_ == 0 {
                                    v___x_1648_ = v___x_1644_;
                                    v_isShared_1649_ = v_isSharedCheck_1653_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1646_);
                                    crate::leanh::lean_dec(v___x_1644_);
                                    v___x_1648_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v_snd_1623_);
                        if crate::leanh::lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                            crate::leanh::lean_inc(v_a_1657_);
                            crate::leanh::lean_dec_ref_known(v___x_1656_, 1);
                            v_____do__lift_1628_ = v_a_1657_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1625_);
                            crate::leanh::lean_dec(v_fst_1622_);
                            crate::leanh::lean_del_object(v___x_1620_);
                            v_a_1658_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                            v_isSharedCheck_1665_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1656_)) as u8;
                            if v_isSharedCheck_1665_ == 0 {
                                v___x_1660_ = v___x_1656_;
                                v_isShared_1661_ = v_isSharedCheck_1665_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1658_);
                                crate::leanh::lean_dec(v___x_1656_);
                                v___x_1660_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1625_, 1, v___x_1629_);
                    v___x_1631_ = v___x_1625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fst_1622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1629_);
                    v___x_1631_ = v_reuseFailAlloc_1635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1621_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1631_);
                    v___x_1633_ = v___x_1620_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
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
                    v_reuseFailAlloc_1652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
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
                    v_reuseFailAlloc_1664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
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
                    v_reuseFailAlloc_1674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
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
    mut v_f_1676_: *mut crate::leanh::LeanObject,
    mut v_goals_1677_: *mut crate::leanh::LeanObject,
    mut v_maxIters_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_1676_, v_goals_1677_, v_maxIters_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
    crate::leanh::lean_dec(v___y_1686_);
    crate::leanh::lean_dec_ref(v___y_1685_);
    crate::leanh::lean_dec(v___y_1684_);
    crate::leanh::lean_dec_ref(v___y_1683_);
    crate::leanh::lean_dec(v___y_1682_);
    crate::leanh::lean_dec_ref(v___y_1681_);
    crate::leanh::lean_dec(v___y_1680_);
    crate::leanh::lean_dec_ref(v___y_1679_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(
    mut v_x_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_1690_ = crate::leanh::lean_ctor_get(v_x_1689_, 1);
    crate::leanh::lean_inc(v_snd_1690_);
    return v_snd_1690_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(
    mut v_x_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_1691_);
    crate::leanh::lean_dec_ref(v_x_1691_);
    return v_res_1692_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_f_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1702_);
                crate::leanh::lean_inc_ref(v___y_1701_);
                crate::leanh::lean_inc(v___y_1700_);
                crate::leanh::lean_inc_ref(v___y_1699_);
                crate::leanh::lean_inc(v___y_1698_);
                crate::leanh::lean_inc_ref(v___y_1697_);
                crate::leanh::lean_inc(v___y_1696_);
                crate::leanh::lean_inc_ref(v___y_1695_);
                v___x_1704_ = crate::leanh::lean_apply_9(
                    v_a_1693_,
                    v___y_1695_,
                    v___y_1696_,
                    v___y_1697_,
                    v___y_1698_,
                    v___y_1699_,
                    v___y_1700_,
                    v___y_1701_,
                    v___y_1702_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1704_) == 0 {
                    v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1713_ = (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v___x_1707_ = v___x_1704_;
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1705_);
                        crate::leanh::lean_dec(v___x_1704_);
                        v___x_1707_ = crate::leanh::lean_box(0);
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1694_);
                    v_a_1714_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1721_ = (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1721_ == 0 {
                        v___x_1716_ = v___x_1704_;
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1714_);
                        crate::leanh::lean_dec(v___x_1704_);
                        v___x_1716_ = crate::leanh::lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1709_ = crate::leanh::lean_apply_1(v_f_1694_, v_a_1705_);
                if v_isShared_1708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1707_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
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
                    v_reuseFailAlloc_1720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
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
    mut v_a_1722_: *mut crate::leanh::LeanObject,
    mut v_f_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1722_, v_f_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    crate::leanh::lean_dec(v___y_1731_);
    crate::leanh::lean_dec_ref(v___y_1730_);
    crate::leanh::lean_dec(v___y_1729_);
    crate::leanh::lean_dec_ref(v___y_1728_);
    crate::leanh::lean_dec(v___y_1727_);
    crate::leanh::lean_dec_ref(v___y_1726_);
    crate::leanh::lean_dec(v___y_1725_);
    crate::leanh::lean_dec_ref(v___y_1724_);
    return v_res_1733_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(
    mut v_f_1735_: *mut crate::leanh::LeanObject,
    mut v_goals_1736_: *mut crate::leanh::LeanObject,
    mut v_maxIters_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1747_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0;
    v___x_1748_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed as *mut core::ffi::c_void, 12, 3);
    crate::leanh::lean_closure_set(v___x_1748_, 0, v_f_1735_);
    crate::leanh::lean_closure_set(v___x_1748_, 1, v_goals_1736_);
    crate::leanh::lean_closure_set(v___x_1748_, 2, v_maxIters_1737_);
    v___x_1749_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_1748_, v___f_1747_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
    return v___x_1749_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(
    mut v_f_1750_: *mut crate::leanh::LeanObject,
    mut v_goals_1751_: *mut crate::leanh::LeanObject,
    mut v_maxIters_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1760_);
    crate::leanh::lean_dec_ref(v___y_1759_);
    crate::leanh::lean_dec(v___y_1758_);
    crate::leanh::lean_dec_ref(v___y_1757_);
    crate::leanh::lean_dec(v___y_1756_);
    crate::leanh::lean_dec_ref(v___y_1755_);
    crate::leanh::lean_dec(v___y_1754_);
    crate::leanh::lean_dec_ref(v___y_1753_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat_x27(
    mut v_stx_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
                crate::leanh::lean_inc(v_stx_1769_);
                v___x_1780_ = l_Lean_Syntax_isOfKind(v_stx_1769_, v___x_1779_);
                if v___x_1780_ == 0 {
                    crate::leanh::lean_dec(v_stx_1769_);
                    v___x_1781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_1781_;
                } else {
                    v___x_1782_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1769_, v___x_1782_);
                    crate::leanh::lean_dec(v_stx_1769_);
                    v___x_1784_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    crate::leanh::lean_inc(v___x_1783_);
                    v___x_1785_ = l_Lean_Syntax_isOfKind(v___x_1783_, v___x_1784_);
                    if v___x_1785_ == 0 {
                        crate::leanh::lean_dec(v___x_1783_);
                        v___x_1786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_1786_;
                    } else {
                        v___x_1787_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_1771_);
                        if crate::leanh::lean_obj_tag(v___x_1787_) == 0 {
                            v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                            crate::leanh::lean_inc(v_a_1788_);
                            crate::leanh::lean_dec_ref_known(v___x_1787_, 1);
                            v___x_1789_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_1789_, 0, v___x_1783_);
                            v___x_1790_ = crate::leanh::lean_unsigned_to_nat(100000);
                            v___x_1791_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_1789_, v_a_1788_, v___x_1790_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
                            if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                                v_a_1792_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                                crate::leanh::lean_inc(v_a_1792_);
                                crate::leanh::lean_dec_ref_known(v___x_1791_, 1);
                                v___x_1793_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_1792_, v_a_1771_);
                                return v___x_1793_;
                            } else {
                                v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                                v_isSharedCheck_1801_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                                if v_isSharedCheck_1801_ == 0 {
                                    v___x_1796_ = v___x_1791_;
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1794_);
                                    crate::leanh::lean_dec(v___x_1791_);
                                    v___x_1796_ = crate::leanh::lean_box(0);
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1783_);
                            v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                            v_isSharedCheck_1809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1787_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1802_);
                                crate::leanh::lean_dec(v___x_1787_);
                                v___x_1804_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
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
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
    mut v_stx_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_a_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1818_);
    crate::leanh::lean_dec_ref(v_a_1817_);
    crate::leanh::lean_dec(v_a_1816_);
    crate::leanh::lean_dec_ref(v_a_1815_);
    crate::leanh::lean_dec(v_a_1814_);
    crate::leanh::lean_dec_ref(v_a_1813_);
    crate::leanh::lean_dec(v_a_1812_);
    crate::leanh::lean_dec_ref(v_a_1811_);
    return v_res_1820_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(
    mut v_00_u03b1_1821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_f_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1823_, v_f_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    return v___x_1834_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(
    mut v_00_u03b1_1835_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_f_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_1835_, v_00_u03b2_1836_, v_a_1837_, v_f_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    crate::leanh::lean_dec(v___y_1846_);
    crate::leanh::lean_dec_ref(v___y_1845_);
    crate::leanh::lean_dec(v___y_1844_);
    crate::leanh::lean_dec_ref(v___y_1843_);
    crate::leanh::lean_dec(v___y_1842_);
    crate::leanh::lean_dec_ref(v___y_1841_);
    crate::leanh::lean_dec(v___y_1840_);
    crate::leanh::lean_dec_ref(v___y_1839_);
    return v_res_1848_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1849_: *mut crate::leanh::LeanObject,
    mut v_x_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1861_, v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
    crate::leanh::lean_dec(v___y_1870_);
    crate::leanh::lean_dec_ref(v___y_1869_);
    crate::leanh::lean_dec(v___y_1868_);
    crate::leanh::lean_dec_ref(v___y_1867_);
    crate::leanh::lean_dec(v___y_1866_);
    crate::leanh::lean_dec_ref(v___y_1865_);
    crate::leanh::lean_dec(v___y_1864_);
    crate::leanh::lean_dec_ref(v___y_1863_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(
    mut v_mvarId_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1873_, v___y_1879_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(
    mut v_mvarId_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
    crate::leanh::lean_dec(v___y_1892_);
    crate::leanh::lean_dec_ref(v___y_1891_);
    crate::leanh::lean_dec(v___y_1890_);
    crate::leanh::lean_dec_ref(v___y_1889_);
    crate::leanh::lean_dec(v___y_1888_);
    crate::leanh::lean_dec_ref(v___y_1887_);
    crate::leanh::lean_dec(v___y_1886_);
    crate::leanh::lean_dec_ref(v___y_1885_);
    crate::leanh::lean_dec(v_mvarId_1884_);
    return v_res_1894_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1898_: u8 = 0;
    v___x_1898_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
    mut v_x_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: u8 = 0;
    let mut v_r_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1899_, v_x_1900_, v_x_1901_);
    crate::leanh::lean_dec(v_x_1901_);
    crate::leanh::lean_dec_ref(v_x_1900_);
    v_r_1903_ = crate::leanh::lean_box((v_res_1902_) as usize);
    return v_r_1903_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(
    mut v_00_u03b2_1904_: *mut crate::leanh::LeanObject,
    mut v_x_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: usize,
    mut v_x_1907_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1908_: u8 = 0;
    v___x_1908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1905_, v_x_1906_, v_x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(
    mut v_00_u03b2_1909_: *mut crate::leanh::LeanObject,
    mut v_x_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
    mut v_x_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5520__boxed_1913_: usize = 0;
    let mut v_res_1914_: u8 = 0;
    let mut v_r_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5520__boxed_1913_ = crate::leanh::lean_unbox_usize(v_x_1911_);
    crate::leanh::lean_dec(v_x_1911_);
    v_res_1914_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_1909_, v_x_1910_, v_x_5520__boxed_1913_, v_x_1912_);
    crate::leanh::lean_dec(v_x_1912_);
    crate::leanh::lean_dec_ref(v_x_1910_);
    v_r_1915_ = crate::leanh::lean_box((v_res_1914_) as usize);
    return v_r_1915_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(
    mut v_00_u03b2_1916_: *mut crate::leanh::LeanObject,
    mut v_keys_1917_: *mut crate::leanh::LeanObject,
    mut v_vals_1918_: *mut crate::leanh::LeanObject,
    mut v_heq_1919_: *mut crate::leanh::LeanObject,
    mut v_i_1920_: *mut crate::leanh::LeanObject,
    mut v_k_1921_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1922_: u8 = 0;
    v___x_1922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1917_, v_i_1920_, v_k_1921_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(
    mut v_00_u03b2_1923_: *mut crate::leanh::LeanObject,
    mut v_keys_1924_: *mut crate::leanh::LeanObject,
    mut v_vals_1925_: *mut crate::leanh::LeanObject,
    mut v_heq_1926_: *mut crate::leanh::LeanObject,
    mut v_i_1927_: *mut crate::leanh::LeanObject,
    mut v_k_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: u8 = 0;
    let mut v_r_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_1923_, v_keys_1924_, v_vals_1925_, v_heq_1926_, v_i_1927_, v_k_1928_);
    crate::leanh::lean_dec(v_k_1928_);
    crate::leanh::lean_dec_ref(v_vals_1925_);
    crate::leanh::lean_dec_ref(v_keys_1924_);
    v_r_1930_ = crate::leanh::lean_box((v_res_1929_) as usize);
    return v_r_1930_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1939_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
    v___x_1940_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1941_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    return v_res_1944_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1972_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6;
    v___x_1973_ = l_Lean_addBuiltinDeclarationRanges(v___x_1971_, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(
    mut v_a_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    return v_res_1975_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(
    mut v_msgData_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = lean_st_ref_get(v___y_1980_);
    v_env_1983_ = crate::leanh::lean_ctor_get(v___x_1982_, 0);
    crate::leanh::lean_inc_ref(v_env_1983_);
    crate::leanh::lean_dec(v___x_1982_);
    v___x_1984_ = lean_st_ref_get(v___y_1978_);
    v_mctx_1985_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1985_);
    crate::leanh::lean_dec(v___x_1984_);
    v_lctx_1986_ = crate::leanh::lean_ctor_get(v___y_1977_, 2);
    v_options_1987_ = crate::leanh::lean_ctor_get(v___y_1979_, 2);
    crate::leanh::lean_inc_ref(v_options_1987_);
    crate::leanh::lean_inc_ref(v_lctx_1986_);
    v___x_1988_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1988_, 0, v_env_1983_);
    crate::leanh::lean_ctor_set(v___x_1988_, 1, v_mctx_1985_);
    crate::leanh::lean_ctor_set(v___x_1988_, 2, v_lctx_1986_);
    crate::leanh::lean_ctor_set(v___x_1988_, 3, v_options_1987_);
    v___x_1989_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
    crate::leanh::lean_ctor_set(v___x_1989_, 1, v_msgData_1976_);
    v___x_1990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1990_, 0, v___x_1989_);
    return v___x_1990_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    crate::leanh::lean_dec(v___y_1995_);
    crate::leanh::lean_dec_ref(v___y_1994_);
    crate::leanh::lean_dec(v___y_1993_);
    crate::leanh::lean_dec_ref(v___y_1992_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(
    mut v_msg_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2004_ = crate::leanh::lean_ctor_get(v___y_2001_, 5);
                v___x_2005_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                v_a_2006_ = crate::leanh::lean_ctor_get(v___x_2005_, 0);
                v_isSharedCheck_2014_ = (!crate::leanh::lean_is_exclusive(v___x_2005_)) as u8;
                if v_isSharedCheck_2014_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2006_);
                    crate::leanh::lean_dec(v___x_2005_);
                    v___x_2008_ = crate::leanh::lean_box(0);
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2004_);
                v___x_2010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2010_, 0, v_ref_2004_);
                crate::leanh::lean_ctor_set(v___x_2010_, 1, v_a_2006_);
                if v_isShared_2009_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2008_, 1);
                    crate::leanh::lean_ctor_set(v___x_2008_, 0, v___x_2010_);
                    v___x_2012_ = v___x_2008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
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
    mut v_msg_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
    crate::leanh::lean_dec(v___y_2019_);
    crate::leanh::lean_dec_ref(v___y_2018_);
    crate::leanh::lean_dec(v___y_2017_);
    crate::leanh::lean_dec_ref(v___y_2016_);
    return v_res_2021_;
}
pub unsafe fn _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ =
        l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0;
    v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(
    mut v_f_2025_: *mut crate::leanh::LeanObject,
    mut v_goals_2026_: *mut crate::leanh::LeanObject,
    mut v_maxIters_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v_fst_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v_snd_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2037_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_2025_, v_goals_2026_, v_maxIters_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
                if crate::leanh::lean_obj_tag(v___x_2037_) == 0 {
                    v_a_2038_ = crate::leanh::lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2050_ = (!crate::leanh::lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2040_ = v___x_2037_;
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2038_);
                        crate::leanh::lean_dec(v___x_2037_);
                        v___x_2040_ = crate::leanh::lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2037_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_dec(v___x_2037_);
                        v___x_2053_ = crate::leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2042_ = crate::leanh::lean_ctor_get(v_a_2038_, 0);
                v___x_2043_ = (crate::leanh::lean_unbox(v_fst_2042_) as u8);
                if v___x_2043_ == 1 {
                    v_snd_2044_ = crate::leanh::lean_ctor_get(v_a_2038_, 1);
                    crate::leanh::lean_inc(v_snd_2044_);
                    crate::leanh::lean_dec(v_a_2038_);
                    if v_isShared_2041_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2040_, 0, v_snd_2044_);
                        v___x_2046_ = v___x_2040_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_snd_2044_);
                        v___x_2046_ = v_reuseFailAlloc_2047_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2040_);
                    crate::leanh::lean_dec(v_a_2038_);
                    v___x_2048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once), _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
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
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
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
    mut v_f_2059_: *mut crate::leanh::LeanObject,
    mut v_goals_2060_: *mut crate::leanh::LeanObject,
    mut v_maxIters_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
    mut v___y_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2069_);
    crate::leanh::lean_dec_ref(v___y_2068_);
    crate::leanh::lean_dec(v___y_2067_);
    crate::leanh::lean_dec_ref(v___y_2066_);
    crate::leanh::lean_dec(v___y_2065_);
    crate::leanh::lean_dec_ref(v___y_2064_);
    crate::leanh::lean_dec(v___y_2063_);
    crate::leanh::lean_dec_ref(v___y_2062_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat1_x27(
    mut v_stx_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2088_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
                crate::leanh::lean_inc(v_stx_2078_);
                v___x_2089_ = l_Lean_Syntax_isOfKind(v_stx_2078_, v___x_2088_);
                if v___x_2089_ == 0 {
                    crate::leanh::lean_dec(v_stx_2078_);
                    v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_2090_;
                } else {
                    v___x_2091_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2092_ = l_Lean_Syntax_getArg(v_stx_2078_, v___x_2091_);
                    crate::leanh::lean_dec(v_stx_2078_);
                    v___x_2093_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    crate::leanh::lean_inc(v___x_2092_);
                    v___x_2094_ = l_Lean_Syntax_isOfKind(v___x_2092_, v___x_2093_);
                    if v___x_2094_ == 0 {
                        crate::leanh::lean_dec(v___x_2092_);
                        v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_2095_;
                    } else {
                        v___x_2096_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_2080_);
                        if crate::leanh::lean_obj_tag(v___x_2096_) == 0 {
                            v_a_2097_ = crate::leanh::lean_ctor_get(v___x_2096_, 0);
                            crate::leanh::lean_inc(v_a_2097_);
                            crate::leanh::lean_dec_ref_known(v___x_2096_, 1);
                            v___x_2098_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_2098_, 0, v___x_2092_);
                            v___x_2099_ = crate::leanh::lean_unsigned_to_nat(100000);
                            v___x_2100_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_2098_, v_a_2097_, v___x_2099_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
                            if crate::leanh::lean_obj_tag(v___x_2100_) == 0 {
                                v_a_2101_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                                crate::leanh::lean_inc(v_a_2101_);
                                crate::leanh::lean_dec_ref_known(v___x_2100_, 1);
                                v___x_2102_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_2101_, v_a_2080_);
                                return v___x_2102_;
                            } else {
                                v_a_2103_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                                v_isSharedCheck_2110_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                                if v_isSharedCheck_2110_ == 0 {
                                    v___x_2105_ = v___x_2100_;
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2103_);
                                    crate::leanh::lean_dec(v___x_2100_);
                                    v___x_2105_ = crate::leanh::lean_box(0);
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2092_);
                            v_a_2111_ = crate::leanh::lean_ctor_get(v___x_2096_, 0);
                            v_isSharedCheck_2118_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2096_)) as u8;
                            if v_isSharedCheck_2118_ == 0 {
                                v___x_2113_ = v___x_2096_;
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2111_);
                                crate::leanh::lean_dec(v___x_2096_);
                                v___x_2113_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
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
                    v_reuseFailAlloc_2117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
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
    mut v_stx_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2127_);
    crate::leanh::lean_dec_ref(v_a_2126_);
    crate::leanh::lean_dec(v_a_2125_);
    crate::leanh::lean_dec_ref(v_a_2124_);
    crate::leanh::lean_dec(v_a_2123_);
    crate::leanh::lean_dec_ref(v_a_2122_);
    crate::leanh::lean_dec(v_a_2121_);
    crate::leanh::lean_dec_ref(v_a_2120_);
    return v_res_2129_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(
    mut v_00_u03b1_2130_: *mut crate::leanh::LeanObject,
    mut v_msg_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2141_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2131_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(
    mut v_00_u03b1_2142_: *mut crate::leanh::LeanObject,
    mut v_msg_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_2142_, v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    crate::leanh::lean_dec(v___y_2151_);
    crate::leanh::lean_dec_ref(v___y_2150_);
    crate::leanh::lean_dec(v___y_2149_);
    crate::leanh::lean_dec_ref(v___y_2148_);
    crate::leanh::lean_dec(v___y_2147_);
    crate::leanh::lean_dec_ref(v___y_2146_);
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2162_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
    v___x_2163_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2164_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    return v_res_2167_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2195_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6;
    v___x_2196_ = l_Lean_addBuiltinDeclarationRanges(v___x_2194_, v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(
    mut v_a_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    return v_res_2198_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Repeat(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Repeat(builtin);
}
